#ifndef _ristretto_h
#define _ristretto_h

#include <sys/types.h>

typedef double rfloat;
typedef uint64_t rint;
typedef uint64_t rbool;

typedef struct {
  rint length;
  rint dims;
  rint data[1];
} rintarray;

typedef struct {
  rint length;
  rint dims;
  char data[0];
} rarray;

rbool ristretto_array_equal(rarray *a, rarray* b);
void ristretto_die(rint error_code);
void *ristretto_alloc(rint bytes);

#endif
