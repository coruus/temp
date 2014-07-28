#include "api.h"
#include "blake2/blake2.h"
#include "ktutils/ktutils.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#include <pthread.h>

#define GKNLEN 64

#define E(LABEL, FMT, ...) do { fprintf(stderr, "err=%u " FMT "\n", err, __VA_ARGS__); goto LABEL; } while (0)

static const uint8_t ds_tagoftags[16] = "tag of tags     ";

#define NUMTHREADS 4

typedef struct {
  uint8_t* out;
  size_t outlen;
  uint8_t* tags;
  size_t taglen;
  const uint8_t* in;
  size_t inlen;
} svi_tinfo;

void* _svi_encrypt_thread(void* _tinfo) {
  svi_tinfo tinfo;
  memcpy(&tinfo, _tinfo, sizeof(tinfo));
}

int _svi_encrypt(uint8_t* out, size_t outlen, uint8_t* tags, size_t taglen, uint8_t* header, size_t headerlen, const uint8_t* in, size_t inlen, uint8_t* gkn, size_t gknlen) {
  if (outlen < (NUMTHREADS * 65536)) {
    // No point in incurring the overhead of multi-threading.
    svi_encrypt_blocks(out, outlen, tags, taglen, gkn, gknlen, 0);
    return 0;
  }
  // Split up the work and launch some threads.
  int err = 0;
  size_t outlen_blocks = outlen / 65536;
  size_t deltablock = outlen_blocks / 4;

  // Pointers to last+1 for assertions to check against.
  #ifndef NDEBUG
  const uint8_t* const outmax = out + outlen;
  const uint8_t* const tagmax = tags + taglen;
  const uint8_t* const inmax = in + inlen;
  #endif


  // Each thread needs to unlock a mutex and then wait
  // on a condition variable. This sets up the relevant
  // machinery.

  // Per-thread mutexes.
  pthread_mutex_t mtxs[NUMTHREADS];
  for (int i = 0; i < NUMTHREADS; i++) {
    err = pthread_mutex_init(&mtxs[i], NULL);
    if (err != 0) { goto cleanup_mutexes; }
  }
  for (int i = 0; i < NUMTHREADS; i++) {
    err |= pthread_mutex_trylock(&mtxs[i]);
  }
  if (err != 0) { goto cleanup_mutexes; }
  // The condition variable.
  pthread_cond_t cond;
  err = pthread_cond_init(&cond, NULL);
  if (err != 0) { goto cleanup_mutexes; }

  // The thread info structures.
  pthread_t threads[NUMTHREADS] = {NULL};
  svi_tinfo tinfo[NUMTHREADS];

  // Start all but the last thread.
  int i = 0;
  for (; i < (NUMTHREADS - 1); i++) {
    //@ assert i != (NUMTHREADS - 1);
    tinfo[i].out = out + i * deltablock * 65536;
    tinfo[i].outlen = deltablock * 65536;
    tinfo[i].tags = tags + i * deltablock * 64;
    tinfo[i].taglen = deltablock * 64;
    tinfo[i].in = in + i * deltablock * 65536;
    tinfo[i].inlen = deltablock * 65536;
    // No overflow.
    /*@ assert i * deltablock * 65536 < RSIZE_MAX; */
    // Note that overflow in the check is possible in C.
    assert((i * deltablock * 65536) < RSIZE_MAX);
    assert((i * deltablock * 65536) >= (deltablock * 65536));
    // Sanity
    assert(tinfo[i].inlen > 0);
    assert(tinfo[i].taglen == (tinfo[i].outlen / 1024));
    assert((tinfo[i].outlen % 65536) == 0);
    // Safety
    assert((tinfo[i].in + tinfo[i].inlen) < inmax);
    assert((tinfo[i].out + tinfo[i].outlen) < outmax);
    assert((tinfo[i].tags + tinfo[i].taglen) < tagmax);

    // The memory regions are valid assuming preconditions.
    /*@ assert \valid(tinfo[i].in[0..tinfo[i].inlen-1]);      */
    /*@ assert \valid(tinfo[i].tags[0..tinfo[i].taglen-1]);   */
    /*@ assert \valid(tinfo[i].out[0..tinfo[i].outlen-1]);    */
    err |= pthread_create(&threads[i], NULL, _svi_encrypt_thread, &tinfo[i]);
    if (err != 0) { goto thread_create_error; }
  }
  // Safety condition: pthread pointer not overwritten
  //@ assert i == (NUMTHREADS - 1);

  // The last thread may be handling an unevenly divided block.
  tinfo[i].out = out + i * deltablock * 65536;
  tinfo[i].outlen = outlen - (deltablock * 65536) * (i - 1);
  tinfo[i].tags = tags + i * deltablock * 65536;
  tinfo[i].taglen = taglen - (deltablock * 64) * (i - 1);
  tinfo[i].in = in + i * deltablock * 65536;
  tinfo[i].inlen = inlen - (deltablock * 65536) * (i - 1);
  // No underflow occurs.
  /*@ assert (outlen - (deltablock * 65536) * (i - 1)) > 0; */
  /*@ assert (taglen - (deltablock * 64) * (i - 1)) > 0;    */
  /*@ assert (inlen - (deltablock * 65536) * (i - 1)) > 0;  */
  // The memory regions are valid assuming preconditions.
  /*@ assert \valid(tinfo[i].in[0..tinfo[i].inlen-1]);      */
  /*@ assert \valid(tinfo[i].tags[0..tinfo[i].taglen-1]);   */
  /*@ assert \valid(tinfo[i].out[0..tinfo[i].outlen-1]);    */
  // All input and output will be used.
  /*@ assert (tinfo[i].out + tinfo[i].outlen) == (out + outlen);    */
  /*@ assert (tinfo[i].in + tinfo[i].inlen) == (in + inlen);        */
  /*@ assert (tinfo[i].tags + tinfo[i].taglen) == (tags + taglen);  */
  // Sanity
  assert(tinfo[i].inlen > 0); // TODO: Is this, in fact, impossible?
  assert(tinfo[i].taglen == (tinfo[i].outlen / 1024));
  assert((tinfo[i].outlen % 65536) == 0);
  // Safety
  assert((tinfo[i].in + tinfo[i].inlen) == inmax);
  assert((tinfo[i].out + tinfo[i].outlen) == outmax);
  assert((tinfo[i].tags + tinfo[i].taglen) == tagmax);

  err |= pthread_create(&threads[i], NULL, _svi_encrypt_thread, &tinfo[i]);
  if (err != 0) { goto kill_threads; }

  // Now that we've succesfully created all of these threads,
  // we can tell them to start work!
  err = pthread_cond_broadcast(&cond);
  if (err != 0) { goto kill_threads; }

  //@assert err = 0;
  int errs[NUMTHREADS] = {0};
  void* errptrs[NUMTHREADS] = {NULL};
  for (int i = 0; i < NUMTHREADS; i++) {
    errptrs[i] = &errs[i];
    err |= pthread_join(threads[i], &errptrs[i]);
  }
  if (err != 0) { goto kill_threads; }

  // Success!

kill_threads:
  for (int i = 0; i < NUMTHREADS; i++) {
    if (threads[i] != NULL) {
      // An error can occur, but there's nothing useful
      // we can do about it.
      pthread_kill(threads[i], 9);
    }
  }
cleanup_mutexes:
  // Errors can occur, but nothing useful can be done
  // about them.
  for (int i = 0; i < NUMTHREADS; i++) {
    pthread_mutex_destroy(&mtxs[i]);
  }

  return err;
}




int svi_encfile(const char* outfn,
                const char* tagfn,
                const char* headerfn,
                const char* infn,
                const uint8_t* gkn) {
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

  err = svi_encrypt(outmf.mem, tagsmf.mem, headermf.mem, inmf.mem);
  if (err != 0) {
    // Something really bad happened. We can't assess what went
    // wrong, so we sanitize all of the output files.
    memset_s(outmf.mem, outmf.length, 0, outmf.length);
    memset_s(tagsmf.mem, tagsmf.length, 0, tagsmf.length);
    memset_s(headermf.mem, headermf.length, 0, headermf.length);
    E(cleanup_headermf, "svi_inplace %u", err);
  }


  uint8_t headertag[64] = {0};
  blake2b_state s;
  blake2b_init_key(&s, 64, gkn, 64);
  blake2b_update(&s, header, HEADERLEN);
  blake2b_final(&s, headertag, 64);
  // Clean up the blake2b state.
  memset_s(&s, sizeof(blake2b_state), 0, sizeof(blake2b_state));



cleanup_headermf: mmfile_close(&headermf);
cleanup_tagsmf:   mmfile_close(&tagsmf);
cleanup_outmf:    mmfile_close(&outmf);
cleanup_inmf:     mmfile_close(&inmf);
done:             return err;
}

