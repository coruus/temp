/* The public API.
 *
 * Note that these functions ARE NOT UNIFORM in their return
 * convention. In particular,
 *   function             failure        success
 *   svi_buflen           SIZE_MAX       < RSIZE_MAX
 *   svi_decrypt_blocks   badblockstart  SIZE_MAX
 *   svi_encrypt_blocks   -1             0
 *
 * This is dangerous C style; but it makes writing useful bindings
 * for high-level languages slightly easier.
 */
#include "salsa-vi8.c"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define ORDERED

/** Returns ceil(`inlen`/BLOCKLEN).
 */
size_t svi_buflen(size_t inlen) {
  if (inlen > RSIZE_MAX) {
    return SIZE_MAX;
  }
  return BLOCKLEN * ((inlen / BLOCKLEN) + ((inlen % BLOCKLEN) != 0));
}

/** Encrypt and tag `inlen` bytes.
 *
 * Define `numblocks` as ceil(inlen/BLOCKLEN).
 *
 * Notes:
 *   - Only inlen bytes are read.
 *   - The input plaintext is zero-extended.
 *   - (uint128_t)(tags+(blocknum*TAGLEN)+16) can be used as a mutex
 *     under certain circumstances; to do so safely in general requires
 *     putting hash_block and salsavi8x128 in another translation unit,
 *     and using a hand-written memcopy
 *
 * @param tags    [out]  Destination for authentication tags.
 * @param taglen  [in]   >= TAGLEN*numblocks
 * @param out     [out]
 * @param outlen  [out]  >= BLOCKLEN*numblocks < RSIZE_MAX
 * @param in      [in]
 * @param inlen   [in]   < RSIZE_MAX
 * @param gkn     [in]   The global key+nonce.
 * @param gknlen  [in]   == 40.
 */
int svi_encrypt_blocks(ORDERED uint8_t* tags,
                       size_t taglen,
                       ORDERED uint8_t* out,
                       size_t outlen,
                       const uint8_t* in,
                       size_t inlen,
                       const uint8_t* gkn,
                       size_t gknlen) {
  if (outlen < inlen) {
    return -1;
  } else if ((outlen % BLOCKLEN) != 0) {
    return -1;
  }

  // The per-block key.
  uint8_t bkn[BKNLEN] = {0};

  uint64_t blocknum = 0;
  size_t remaining = inlen;
  while (remaining >= BLOCKLEN) {
    // Derive the key for this block.
    block_kdf(bkn, gkn, blocknum, 0);

    // The safety property is guaranteed by AtE modes.
    block_encrypt(tags, out, bkn);

    // Increment the counters.
    tags += TAGLEN;
    out  += BLOCKLEN;
    in   += BLOCKLEN;
    blocknum += 128;
  }
  if (remaining) {
    // We need to zero-extend the input.

    // Derive the key for this block.
    uint8_t bkn[BKNLEN] = {0};
    block_kdf(bkn, gkn, blocknum, 0);

    // Copy the remaining input to a zero-filled buffer.
    uint8_t buf[BLOCKLEN] = {0};
    memcpy(buf, in, remaining);
    block_encrypt(tags, buf, bkn);
    memcpy(out, buf, BLOCKLEN);
    memcpy(tags, tags, TAGLEN);
  }
  memset_s(bkn, BKNLEN, 0, BKNLEN);
  return 0;
}

/** Authenticate and decrypt blocks.
 *
 * If outlen < inlen, the output will be truncated to outlen
 * bytes.
 *
 * No unauthenticated plaintext is ever written to out. But
 * out is not cleared if a tag fails to validate (that is,
 * all previous plaintext blocks will remain).
 *
 * @param out    [out]
 * @param outlen [in]   < RSIZE_MAX
 * @param tags   [in]
 * @param taglen [in]   numblocks*TAGLEN
 * @param in     [in]
 * @param inlen  [in]   inlen >= outlen && 0 mod BLOCKLEN
 * @param gkn    [in]
 * @param gknlen [in]   == GKNLEN
 *
 * Returns SIZE_MAX on success, the index of the first byte of the
 * first bad block on failure.
 */
size_t svi_decrypt_blocks(uint8_t* out,
                          size_t outlen,
                          const uint8_t* tags,
                          size_t taglen,
                          const uint8_t* in,
                          size_t inlen,
                          const uint8_t* gkn,
                          size_t gknlen) {
  int err = 0;
  uint64_t blocknum = 0;
  size_t remaining = inlen;

  while (remaining >= BLOCKLEN) {
    // Derive the key for this block.
    uint8_t bkn[BKNLEN] = {0};
    block_kdf(bkn, gkn, blocknum, 0);

    // The safety property is guaranteed by AtE modes.
    err = block_decrypt(out, tags, in, bkn);
    if (err != 0) {
      return blocknum;
    }

    // Increment the counters.
    tags += TAGLEN;
    out += BLOCKLEN;
    in += BLOCKLEN;
    blocknum += 128;
  }
  if (remaining) {
    // We need to zero-extend the output, because sub-block-
    // truncated output has been requested.

    // Derive the key for this block.
    uint8_t bkn[BKNLEN] = {0};
    block_kdf(bkn, gkn, blocknum, 0);

    // Copy the remaining input to a zero-filled buffer.
    uint8_t buf[BLOCKLEN] = {0};
    err = block_decrypt(buf, tags, in, bkn);
    if (err != 0) {
      return blocknum;
    }

    // Only copy `remaining` bytes out.
    memcpy(out, buf, remaining);
  }
  return SIZE_MAX;
}
