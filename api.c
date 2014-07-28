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

#include <assert.h>
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

int svi_encrypt_blocks(ORDERED uint8_t* tags, size_t taglen,
                       ORDERED uint8_t* out, size_t outlen,
                       const uint8_t* in, size_t inlen,
                       const uint8_t* gkn, size_t gknlen,
                       uint64_t blocknum) {
  if (outlen < inlen) {
    return -1;
  } else if ((outlen % BLOCKLEN) != 0) {
    return -1;
  }

  const uint8_t* const tagsmax = tags + taglen;
  const uint8_t* const outmax = out + outlen;
  const uint8_t* const inmax = in + inlen;


  // The per-block key.
  uint8_t bkn[BKNLEN] = {0};

  size_t remaining = inlen;
  while (remaining >= BLOCKLEN) {
    assert(tagsmax > tags);
    assert(outmax > out);
    assert(inmax > in);
    // Derive the key for this block.
    block_kdf(bkn, gkn, blocknum, 0);

    // The safety property is guaranteed by AtE modes.
    block_encrypt(tags, out, bkn);

    // Increment the counters.
    tags += TAGLEN;
    out  += BLOCKLEN;
    in   += BLOCKLEN;
    blocknum += 128;
    remaining -= BLOCKLEN;
  }
  if (remaining) {
    // We need to zero-extend the input.
    assert(tagsmax > tags);
    assert(outmax > out);
    assert(inmax > in);

    // Derive the key for this block.
    uint8_t bkn[BKNLEN] = {0};
    block_kdf(bkn, gkn, blocknum, 0);

    // Copy the remaining input to a zero-filled buffer.
    uint8_t buf[BLOCKLEN] = {0};
//    memcpy(buf, in, remaining);
    block_encrypt(tags, buf, bkn);
    memcpy(out, buf, BLOCKLEN);
    memcpy(tags, tags, TAGLEN);
  }
  memset_s(bkn, BKNLEN, 0, BKNLEN);
  return 0;
}

/*@ behavior rte:
  @   assumes    out == NULL
  @           || outlen > RSIZE_MAX
  @           || tags == NULL
  @           || taglen > RSIZE_MAX
  @           || taglen < numblocks(outlen)*TAGLEN;
  @           || in == NULL
  @           || inlen > RSIZE_MAX
  @           || inlen < outlen
  @           || gkn == NULL
  @           || gknlen != GKNLEN;
  @   ensures \result == SIZE_MAX;
  @   assigns \nothing;
  @*/
size_t svi_decrypt_blocks(uint8_t* out,
                          size_t outlen,
                          const uint8_t* tags,
                          size_t taglen,
                          const uint8_t* in,
                          size_t inlen,
                          const uint8_t* gkn,
                          size_t gknlen,
                          uint64_t blocknum) {
#if defined(FRAMAC) || !defined(NDEBUG)
  const uint8_t* const tagmax = tags + taglen;
  const uint8_t* const inmax = in + inlen;
  const uint8_t* const outmax = out + outlen;
#endif // defined(FRAMAC) || !defined(NDEBUG)

  size_t err = 0;
  size_t remaining = outlen;

  uint8_t bkn[BKNLEN];

  while (remaining >= BLOCKLEN) {
    // Derive the key for this block.
    block_kdf(bkn, gkn, blocknum, 0);

    // The safety property is guaranteed by AtE modes.
    err = block_decrypt(out, tags, in, bkn);
    if (err != 0) {
      err = blocknum;
      goto cleanup;
    }

    // Increment the counters.
    tags += TAGLEN;
    out += BLOCKLEN;
    in += BLOCKLEN;
    blocknum += 128;
    remaining -= BLOCKLEN;

    assert(tags <= tagmax);
    assert(out <= outmax);
    assert(in <= inmax);
    //@ assert(tags <= tagmax);
    //@ assert(out <= outmax);
    //@ assert(in <= inmax);
  }
  //@ assert remaining < BLOCKLEN;
  if (remaining) {
    //@ assert 0 < remaining < BLOCKLEN;

    // We need to zero-extend the output, because sub-block-
    // truncated output has been requested.

    // Derive the key for this block.
    block_kdf(bkn, gkn, blocknum, 0);

    // Copy the remaining input to a zero-filled buffer.
    uint8_t buf[BLOCKLEN] = {0};
    err = block_decrypt(buf, tags, in, bkn);
    memset_s(buf, BLOCKLEN, 0, BLOCKLEN);
    if (err != 0) {
      err = blocknum;
      goto cleanup;
    }

    // Only copy `remaining` bytes out.
    //@ assert \valid(out[0..remaining-1]);
    //@ assert remaining < BLOCKLEN;
    memcpy(out, buf, remaining);
  }
cleanup:
  memset_s(bkn, BKNLEN, 0, BKNLEN);
  return SIZE_MAX;
}
/*
#include "print-impl.h"
#define N 64
#define TAGLEN 64
#define BLOCKLEN 65536
int main(void) {
  uint8_t tags[N*TAGLEN] = {0};
  uint8_t io[N*BLOCKLEN] = {0};
  uint8_t gkn[GKNLEN] = {0};
  uint64_t blocknum = 0;
  svi_encrypt_blocks(tags, N*TAGLEN, io, N*BLOCKLEN, io, N*BLOCKLEN, gkn, GKNLEN, 0);
  //int err = svi_decrypt_blocks(io, N*BLOCKLEN, tags, N*TAGLEN, io, N*BLOCKLEN, gkn, GKNLEN, 0);
  printbuf(tags, N*TAGLEN);
  printbuf(io, 128);
}*/
/** The header format:
 *    32-byte nonce
 *    xorlen = uint64 (original length) ^ hash(k=gkn, nonce)
 *    64-byte tag of tags == hash(k=gkn, nonce || tags)
 *
int svi_mkheader(uint8_t* header, size_t headerlen,
                 uint8_t* tags, size_t taglen,
                 const uint8_t* gkn, size_t gknlen,
                 uint64_t inlen) {
}*/
