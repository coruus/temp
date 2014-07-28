/** Warning: This is somewhat complex. **/
#include "api.h"
#include "blake2/blake2.h"
#include "ktutils/ktutils.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <pthread.h>

#define GKNLEN 64

#define E(LABEL, FMT, ...)                                  \
  do {                                                      \
    fprintf(stderr, "err=%u " FMT "\n", err, __VA_ARGS__);  \
    goto LABEL;                                             \
  } while (0)

static const uint8_t ds_tagoftags[16] = "tag of tags     ";

#define NUMTHREADS 4

typedef struct {
  uint8_t* out;
  size_t outlen;
  uint8_t* tags;
  size_t taglen;
  const uint8_t* in;
  size_t inlen;
  const uint8_t* gkn;
  size_t gknlen;
  uint64_t blocknum;
  pthread_cond_t* cond;
} svi_tinfo;

#if 1
_Noreturn void* _svi_encrypt_thread_entry(void* _tinfo) {
  int err = 0;
  svi_tinfo tinfo;
  memcpy(&tinfo, _tinfo, sizeof(tinfo));
  pthread_mutex_t mtx;
  err = pthread_mutex_init(&mtx, NULL);
  if (err != 0) { goto done; }
  err = pthread_mutex_lock(&mtx);
  if (err != 0) { goto destroy_mutex; }
  err = pthread_cond_wait(tinfo.cond, &mtx);
  if (err != 0) { goto destroy_mutex; }

  svi_encrypt_blocks(tinfo.tags, tinfo.taglen, tinfo.out, tinfo.outlen,
                     tinfo.in, tinfo.inlen, tinfo.gkn, tinfo.gknlen,
                     tinfo.blocknum);

destroy_mutex: pthread_mutex_destroy(&mtx);
done: pthread_exit(NULL);
}

int _svi_encrypt(uint8_t* out, size_t outlen,
                 uint8_t* tags, size_t taglen,
                 uint8_t* header, size_t headerlen,
                 const uint8_t* in, size_t inlen,
                 const uint8_t* gkn, size_t gknlen) {
  int err = 0;
  if (outlen < (NUMTHREADS * 65536)) {
    // No point in incurring the overhead of multi-threading.
    err = svi_encrypt_blocks(tags, taglen, out, outlen, in, inlen, gkn, gknlen, 0);
    if (err != 0) { return err; }
    //err = svi_mkheader(header, headerlen, tags, taglen, gkn, gknlen, inlen);
    return err;
  }
  // Split up the work and launch some threads.
  size_t outlen_blocks = outlen / 65536;
  size_t deltablock = outlen_blocks / 4;

  // Pointers to last+1 for assertions to check against.
  #ifndef NDEBUG
  const uint8_t* const outmax = out + outlen;
  const uint8_t* const tagmax = tags + taglen;
  const uint8_t* const inmax = in + inlen;
  #endif

  // Each thread will create a mutex and then block on the
  // condition variable; this ensures that we don't do anything
  // if we fail to launch all threads.
  pthread_cond_t cond;
  err = pthread_cond_init(&cond, NULL);
  if (err != 0) { goto cleanup_condition; }

  // The thread info structures.
  pthread_t threads[NUMTHREADS] = {NULL};
  svi_tinfo tinfo[NUMTHREADS];

  // Start all but the last thread.
  int i = 0;
  // No overflow can occur (if the operations are constructed properly).
  /*@ assert (NUMTHREADS * deltablock * 65536) < RSIZE_MAX; */
  for (; i < (NUMTHREADS - 1); i++) {
    /*@ assert i != (NUMTHREADS - 1); */ // trivial fact to help WP.

    // No overflow occurs.
    assert((i * deltablock * 65536) < RSIZE_MAX);
    /*@ assert i * deltablock * 65536 < RSIZE_MAX; */

    tinfo[i].in     = in   + i*deltablock*65536;
    tinfo[i].out    = out  + i*deltablock*65536;
    tinfo[i].tags   = tags + i*deltablock*64;
    tinfo[i].inlen  = deltablock * 65536;
    tinfo[i].outlen = deltablock * 65536;
    tinfo[i].taglen = deltablock * 64;

    tinfo[i].cond     = &cond;
    tinfo[i].blocknum = deltablock * i;
    tinfo[i].gkn      = gkn;
    tinfo[i].gknlen   = gknlen;

    /**** assertions ****/
    // Trivial conditions.
    assert(tinfo[i].inlen > 0);
    assert(tinfo[i].inlen < inlen);
    assert(tinfo[i].outlen > 0);
    assert(tinfo[i].outlen < outlen);
    assert(tinfo[i].taglen > 0);
    assert(tinfo[i].taglen < taglen);
    // Complex correctness conditions.
    assert(tinfo[i].taglen == (tinfo[i].outlen / 1024));
    assert((tinfo[i].outlen % 65536) == 0);
    // High-level safety conditions.
    assert((tinfo[i].in + tinfo[i].inlen) < inmax);
    assert((tinfo[i].out + tinfo[i].outlen) < outmax);
    assert((tinfo[i].tags + tinfo[i].taglen) < tagmax);
    /*@ assert \valid(tinfo[i].in[0..tinfo[i].inlen-1]);      */
    /*@ assert \valid(tinfo[i].tags[0..tinfo[i].taglen-1]);   */
    /*@ assert \valid(tinfo[i].out[0..tinfo[i].outlen-1]);    */
    /**** end assertions ****/

    err |= pthread_create(&threads[i],
                          NULL,
                          _svi_encrypt_thread_entry,
                          &tinfo[i]);
    if (err != 0) { goto kill_threads; }
  }
  // Safety condition: pthread pointer not overwritten
  //@ assert i == (NUMTHREADS - 1);

  // The last thread may be handling an unevenly divided block.
  tinfo[i].in     = in   + i*deltablock*65536;
  tinfo[i].out    = out  + i*deltablock*65536;
  tinfo[i].tags   = tags + i*deltablock*64;
  tinfo[i].inlen  = (deltablock * 65536);
  tinfo[i].outlen = (deltablock * 65536);
  tinfo[i].taglen = (deltablock * 64);

  tinfo[i].cond     = &cond;
  tinfo[i].blocknum = deltablock * i;
  tinfo[i].gkn      = gkn;
  tinfo[i].gknlen   = gknlen;
  /**** assertions ****/
  // Frama-C: No underflow occurs.
  /*@ assert (outlen - (deltablock * 65536) * (i - 1)) > 0; */
  /*@ assert (taglen - (deltablock * 64) * (i - 1)) > 0;    */
  /*@ assert (inlen - (deltablock * 65536) * (i - 1)) > 0;  */
  // Frama-C: The memory regions are valid.
  /*@ assert \valid(tinfo[i].in[0..tinfo[i].inlen-1]);      */
  /*@ assert \valid(tinfo[i].tags[0..tinfo[i].taglen-1]);   */
  /*@ assert \valid(tinfo[i].out[0..tinfo[i].outlen-1]);    */
  // Safety
  assert(tinfo[i].inlen > 0); // TODO: Is this, in fact, impossible?
  assert(tinfo[i].taglen == (tinfo[i].outlen / 1024));
  assert((tinfo[i].outlen % 65536) == 0);
  // Correctness
  assert((tinfo[i].in + tinfo[i].inlen) == inmax);
  assert((tinfo[i].out + tinfo[i].outlen) == outmax);
  assert((tinfo[i].tags + tinfo[i].taglen) == tagmax);
  // Frama-C: All input and output will be used.
  /*@ assert (tinfo[i].out + tinfo[i].outlen) == (out + outlen);    */
  /*@ assert (tinfo[i].in + tinfo[i].inlen) == (in + inlen);        */
  /*@ assert (tinfo[i].tags + tinfo[i].taglen) == (tags + taglen);  */
  /**** assertions ****/

  err |= pthread_create(&threads[i], NULL, _svi_encrypt_thread_entry, &tinfo[i]);
  if (err != 0) { goto kill_threads; }

  // Now that we've succesfully created all of these threads,
  // we can tell them to start work!
  err = pthread_cond_broadcast(&cond);
  if (err != 0) { goto kill_threads; }

  //@assert err = 0;
  int errs[NUMTHREADS] = {0};
  for (int i = 0; i < NUMTHREADS; i++) {
    err |= pthread_join(threads[i], NULL);
  }
  if (err != 0) { goto kill_threads; }

  // Success!
  /*@ assert err == 0; */ // trivial fact for WP
  // Now, the non-parallelizable part: making the header.
//  err = svi_mkheader(header, headerlen, tags, taglen, gkn, gknlen, inlen);
  goto cleanup_condition;

kill_threads:
  // We can't do anything useful about an error in pthread_kill
  for (int i = 0; i < NUMTHREADS; i++) {
    if (threads[i] != NULL) { pthread_kill(threads[i], 9); }
  }
cleanup_condition:
  // Errors can occur, but nothing useful can be done
  // about them.
  pthread_cond_destroy(&cond);
  return err;
}
#endif


int svi_encfile(const char* outfn,
                const char* tagfn,
                const char* headerfn,
                const char* infn,
                const uint8_t* gkn, size_t gknlen) {
  int err = 0;
  mmfile inmf;
  err = mmfile_open(&inmf, infn, O_RDONLY);
  if (err != 0) { E(done, "mmfile_open %s", infn); }
  uint64_t outlen = svi_buflen(inmf.length);
  uint64_t numblocks = outlen / 65536;
  uint64_t taglen = numblocks * 64;

  mmfile outmf;
  err = mmfile_create(&outmf, outfn, outlen);
  if (err != 0) { E(cleanup_inmf, "mmfile_create %s", infn); }

  mmfile tagsmf;
  err = mmfile_create(&tagsmf, tagfn, taglen);
  if (err != 0) { E(cleanup_outmf, "mmfile_create %s", tagfn); }

  mmfile headermf;
  err = mmfile_create(&headermf, headerfn, 4096);
  if (err != 0) { E(cleanup_tagsmf, "mmfile_create %s", headerfn); }
  memset_s(headermf.mem, headermf.length, 0, headermf.length);

  /*err = _svi_encrypt(outmf.mem, outmf.length,
                     tagsmf.mem, tagsmf.length,
                     headermf.mem, headermf.length,
                     inmf.mem, inmf.length,
                     gkn, gknlen);*/
  err = svi_encrypt_blocks(tagsmf.mem, tagsmf.length,
                           outmf.mem, outmf.length,
                           inmf.mem, inmf.length,
                           gkn, gknlen,
                           0);

  if (err != 0) {
    // Something really bad happened. We can't assess what went
    // wrong, so we sanitize all of the output files.
    memset_s(outmf.mem, outmf.length, 0, outmf.length);
    memset_s(tagsmf.mem, tagsmf.length, 0, tagsmf.length);
    memset_s(headermf.mem, headermf.length, 0, headermf.length);
    E(cleanup_headermf, "svi_inplace %u", err);
  }

cleanup_headermf: mmfile_close(&headermf);
cleanup_tagsmf:   mmfile_close(&tagsmf);
cleanup_outmf:    mmfile_close(&outmf);
cleanup_inmf:     mmfile_close(&inmf);
done:             return err;
}

int main(void) {
  uint8_t gkn[GKNLEN] = {0};
  uint64_t start = __builtin_readcyclecounter();
  int err = svi_encfile("test.out", "test.tags", "test.header", "test.in", gkn, GKNLEN);
  double cpb = (double)(__builtin_readcyclecounter() - start) / (double)(1024*1024*16);
  printf("cpb = %f\n", cpb);
  return err;
}
