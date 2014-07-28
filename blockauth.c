#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <sodium.h>

#define XSALSA_NONCELEN SIZE_C(24)
#define XSALSA_KEYLEN   SIZE_C(32)
#define BLAKE2_KEYLEN   SIZE_C(64)

#define SIZE_C(C) ((size_t)(C))
#define PAGELEN     SIZE_C(4096)
#define PPB         SIZE_C(32)
#define BLOCKLEN    SIZE_C(PPB * PAGELEN)
#define TAGLEN      SIZE_C(64)  // The length of authentication tags.
#define BKNLEN      (XSALSA_NONCELEN + XSALSA_KEYLEN) // The length of the block key+nonce
#define HASHKEYLEN  BKNLEN   // must be <= BKNLEN
#define GKEYLEN     SIZE_C(32)
#define GNONCELEN   SIZE_C(32)

#define scribble(WHAT, WHATLEN)                 \
  memset_s((WHAT), (WHATLEN), 0xcc, (WHATLEN))

//static_assert(HASHKEYLEN <= BKLEN);
//static_assert(HASHKEYLEN <= BLAKE2_KEYLEN);

#define ghash_state crypto_generichash_state
#define ghash_init crypto_generichash_init
#define ghash_update(state, in, inlen) crypto_generichash_update((state), (uint8_t*)(in), (inlen))
#define ghash_final crypto_generichash_final
#define keyed_hash crypto_generichash
#define stream_xor crypto_stream_xsalsa20_xor
// TODO(dlg): replace with kt_memcompare
#define verify64(S1, S2, SLEN) \
	memcmp(S1, S2, SLEN)

#define start_timer(NAME) \
  uint64_t NAME##_start = __builtin_readcyclecounter()

#define stop_timer(NAME) \
  uint64_t NAME##_end = __builtin_readcyclecounter()

/** Derive the block key/nonce for a block.
 *
 * The overhead is minimal; this is called once for every block,
 * with BLOCKLEN = 64kiB.
 */
static inline void derive_bkn(uint8_t* bkn,
		              const uint8_t* const gkey,
                              const uint8_t* const gnonce,
                              const uint64_t blockgen,
                              const uint64_t blocknum) {
  ghash_state state;
  ghash_init(&state, gkey, GKEYLEN, BKNLEN);  // Initialize the keyed hash.
  ghash_update(&state, gnonce, GNONCELEN);    // Update with the nonce.
  ghash_update(&state, &blockgen, 8);         // Update with the block generation.
  ghash_update(&state, &blocknum, 8);         // Update with the block number.
  ghash_final(&state, bkn, BKNLEN);        // `BLKLEN` digest to `bkn`
  scribble(&state, sizeof(ghash_state));
}

static inline void _encrypt_block(uint8_t* tag, uint8_t* block,  uint8_t* bkn) {
  // Note: The count for stream_xor always starts at zero within a block;
  // the block number has already been incorporated into `bkn`.
  // stream_xor(c, m, mlen, n, k)
  stream_xor(block, block, BLOCKLEN, bkn, bkn+XSALSA_NONCELEN);
  // crypto_generichash(o, olen, m, mlen, k, kley)
  keyed_hash(tag, TAGLEN, block, BLOCKLEN, bkn, HASHKEYLEN);
}

/** A wrapper to derive a block key and encrypt a block.
 */
static inline void encrypt_block(uint8_t* tag,
		 uint8_t* block,
		 const uint8_t* gkey,
		 const uint8_t* gnonce,
		 const uint64_t blockgen,
		 const uint64_t blocknum) {
  uint8_t bkn[BKNLEN] = {0};
  // Derive the block key+nonce.
  derive_bkn(bkn, gkey, gnonce, blockgen, blocknum);
  _encrypt_block(tag, block, bkn);
  scribble(bkn, BKNLEN);
}

/** Authenticate the input and decrypt the block.
 *
 * Return is != 0 iff there is an error.
 */
static inline int _decrypt_block(uint8_t* tag, uint8_t* block, const uint8_t* kn) {
  uint8_t ptag[TAGLEN] = {0};
  keyed_hash(ptag, TAGLEN, block, BLOCKLEN, kn, HASHKEYLEN);
  size_t diffs = 0;//verify64(tag, ptag, TAGLEN);
  if (diffs != 0) {
    return -1;
  }
  stream_xor(block, block, BLOCKLEN, kn, kn+XSALSA_NONCELEN);
  return 0;
}

/** A wrapper to derive a block key and decrypt a block.
*/
static inline int decrypt_block(uint8_t* tag,
		 uint8_t* block,
		 const uint8_t* gkey,
		 const uint8_t* gnonce,
		 const uint64_t blockgen,
		 const uint64_t blocknum) {
  uint8_t bkn[BKNLEN] = {0};
  // Derive the block key+nonce.
  derive_bkn(bkn, gkey, gnonce, blockgen, blocknum);
  int err = _decrypt_block(tag, block, bkn);
  scribble(bkn, BKNLEN);
}

/** A simple high-level interface to encrypt and tag all
 *  blocks of the input.
 *
 *  @param tags[out]     where to store the tags
 *  @param tagslen[in]   must be TAGLEN * (iolen / BLOCKLEN)
 *  @param io[in,out]    iolen bytes of data to encrypt and tag
 *  @param iolen[in]     must be 0 % BLOCKLEN
 *  @param blockgens[in] must be a pointer to an array of numblocks uint64s
 */
void encrypt_blocks(uint8_t* tags, size_t tagslen,
		    uint8_t* io, size_t iolen,
		    const uint8_t* gkey, size_t gkeylen,
		    const uint8_t* gnonce,
		    const uint64_t* blockgens,
		    uint64_t blocknum) {
  // TODO(dlg): input validation
  for (uint64_t i = 0; i < iolen; i += BLOCKLEN) {
//    printf("on %u\n", i);
    encrypt_block(tags, io, gkey, gnonce, blockgens, blocknum);
    // Increment the block number.
    blocknum++;
    // Advance the pointers.
    blockgens++;
    io += BLOCKLEN;
    tags += TAGLEN;
  }
}

#include "print-impl.h"

/** A simple high-level interface to verify the tags and decrypt
 *  all blocks of the input.
 *
 *  @param tags[out]     where to store the tags
 *  @param tagslen[in]   must be TAGLEN * (iolen / BLOCKLEN)
 *  @param io[in,out]    iolen bytes of data to encrypt and tag
 *  @param iolen[in]     must be 0 % BLOCKLEN
 *  @param blockgens[in] must be a pointer to an array of numblocks uint64s
 */
int decrypt_blocks(uint8_t* tags, size_t tagslen,
		    uint8_t* io, size_t iolen,
		    const uint8_t* gkey, size_t gkeylen,
		    const uint8_t* gnonce,
		    const uint64_t* blockgens,
		    uint64_t blocknum) {
  // TODO(dlg): input validation
  for (uint64_t i = 0; i < iolen; i += BLOCKLEN) {
    //printf("on %u\n", i);
    //printbuf(tags, TAGLEN);
    int err = decrypt_block(tags, io, gkey, gnonce, blockgens, blocknum);
    if (err) {
      return err;
    }
    // Increment the block number.
    blocknum++;
    // Advance the pointers.
    blockgens++;
    io += BLOCKLEN;
    tags += TAGLEN;
  }
  return 0;
}

int main(void) {
  #define N 64
  int err = 0;
  uint8_t* tags= valloc(TAGLEN*N);
  if (tags == NULL) { goto done; }
  uint8_t* io = valloc(BLOCKLEN*N);
  if (io == NULL) { goto free_tags; }
  uint64_t* blockgens = valloc(N*8);
  if (blockgens == NULL) { goto free_io; }

  uint8_t gnonce[GNONCELEN] = {0};
  uint8_t k[GKEYLEN] = {0};
  start_timer(encrypt);
  encrypt_blocks(tags, TAGLEN*N, io, BLOCKLEN*N, k, GKEYLEN, gnonce, blockgens, 0);
  stop_timer(encrypt);
  printf("%zu bytes encrypted at %f MB/s\n", (encrypt_end - encrypt_start) / (double)(BLOCKLEN*N));
//  printbuf(tags, TAGLEN*N);
  //printbuf(io, BLOCKLEN);
  err = decrypt_blocks(tags, TAGLEN*N, io, BLOCKLEN*N, k, GKEYLEN, gnonce, blockgens, 0);
 // printbuf(tags, TAGLEN*N);
  //printbuf(io, BLOCKLEN);
  if (err != 0) {
    printf("ERROR\n");
  }
  printf("\n%u", tags[0]);
  printf("%u\n", io[0]);

free_blockgens: free(blockgens); blockgens = NULL;
free_io:        free(io); io = NULL;
free_tags:      free(tags); tags = NULL;
done:           return err;
} 

