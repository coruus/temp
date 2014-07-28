#ifndef SVI_API_H
#define SVI_API_H
#include <stdint.h>
#include <stdlib.h>
#define ORDERED
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
size_t svi_decrypt_blocks(uint8_t* out, size_t outlen,
                          const uint8_t* tags, size_t taglen,
                          const uint8_t* in, size_t inlen,
                          const uint8_t* gkn, size_t gknlen,
                          uint64_t blocknum);
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
 *     and using a hand-written (unoptimizable) memcpy
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
int svi_encrypt_blocks(ORDERED uint8_t* tags, size_t taglen,
                       ORDERED uint8_t* out, size_t outlen,
                       const uint8_t* in, size_t inlen,
                       const uint8_t* gkn, size_t gknlen,
                       uint64_t blocknum);
size_t svi_buflen(size_t inlen);
#endif // !defined(SVI_API_H)
