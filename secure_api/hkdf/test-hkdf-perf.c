#include "kremlib.h"
#include "testlib.h"
#include "Crypto_HKDF.h"
#include "hacl_test_utils.h"

typedef unsigned long long TestLib_cycles, cycles;


void print_results(char *txt, double t1, uint64_t d1, int rounds, int plainlen){
  printf("Testing: %s\n", txt);
  printf("Cycles for %d times %d bytes: %" PRIu64 " (%.2fcycles/byte)\n", rounds, plainlen, d1, (double)d1/plainlen/rounds);
  printf("User time for %d times %d bytes: %f (%fus/byte)\n", rounds, plainlen, t1/CLOCKS_PER_SEC, (double)t1*1000000/CLOCKS_PER_SEC/plainlen/rounds);
}


#define ROUNDS 10000
#define HASHSIZE 32
#define BLOCKSIZE 64
#define IKMLEN (16*1024)
#define OKMLEN 128
#define INFOLEN 512

int32_t perf_hkdf_sha256() {
  double hacl_cy, hacl_utime;
  cycles a,b;
  clock_t t1,t2;
  
  uint32_t saltlen = BLOCKSIZE * sizeof(char);
  uint8_t* salt = malloc(saltlen);

  uint32_t ikmlen = IKMLEN * sizeof(char);
  uint8_t* ikm = malloc(ikmlen);

  uint8_t* prk = malloc(ROUNDS * HASHSIZE * sizeof(char));

  if (! (read_random_bytes(ikmlen, ikm)))
    return 1;
  if (! (read_random_bytes(saltlen, salt)))
    return 1;

  // HKDF-Extract
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++) {
    Crypto_HKDF_hkdf_extract(Crypto_HMAC_alg_SHA256,
                             prk + HASHSIZE * i, salt, saltlen, ikm, ikmlen);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
   
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  print_results("HACL HKDF-Extract-SHA2-256", hacl_utime, hacl_cy, ROUNDS, saltlen + ikmlen);


  // HKDF-Expand
  uint8_t* okm = malloc(ROUNDS * OKMLEN * sizeof(char));
  uint32_t infolen = INFOLEN * sizeof(char);
  uint8_t* info = malloc(infolen);
  
  if (! (read_random_bytes(infolen, info)))
    return 1;
 
  t1 = clock();
  a = TestLib_cpucycles_begin();
  for (int i = 0; i < ROUNDS; i++) {
    Crypto_HKDF_hkdf_expand(Crypto_HMAC_alg_SHA256,
                            okm + OKMLEN * i, prk, HASHSIZE, info, infolen, OKMLEN);
  }
  b = TestLib_cpucycles_end();
  t2 = clock();
   
  hacl_cy = (double)b - a;
  hacl_utime = (double)t2 - t1;
  // Not counting the HASHSIZE + 1 extra input bytes in each okmlen/HASHSIZE HMAC call 
  print_results("HACL HKDF-Expand-SHA2-256", hacl_utime, hacl_cy, ROUNDS, HASHSIZE + infolen);

  return exit_success;
}
  
int32_t main(int argc, char *argv[])
{
    int32_t res = perf_hkdf_sha256();
    return res;
}
