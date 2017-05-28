#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "ristretto.h"

static rintarray *
alloc_rintarray(size_t length)
{
    rintarray *a = (rintarray *) calloc(length + 2, sizeof(rint));
    if (a == NULL) {
      printf("allocation of %ld ints failed\n", length);
      exit(1);
    }
    a->length = length;
    a->dims = 1;
    return a;
}

static rintarray *
c2rstring(char *s)
{
  rintarray *a = alloc_rintarray(strlen(s));
  int i = 0;
  while (*s) {
    a->data[i] = (rint) *s;
    s++;
    i++;
  }
  return a;
}

rintarray *
boolean2str(rbool b)
{
  if (b)
    return c2rstring("true");
  else
    return c2rstring("false");
}

rintarray *
float2str(rfloat b)
{
  char buf[256];
  snprintf(buf, sizeof(buf), "%f", b);
  return c2rstring(buf);
}

rintarray *
int2str(rint b)
{
  char buf[256];
  snprintf(buf, sizeof(buf), "%lld", b);
  return c2rstring(buf);
}


void
print(rintarray *a)
{
  size_t n = (size_t) a->length;
  for (int i = 0; i < n; i++) {
    putchar((char) a->data[i]);
  }
}


void
println(rintarray *a)
{
  print(a);
  putchar('\n');
  fflush(stdout);
}

rintarray *
readline()
{
  static rintarray EOF_ARRAY = {
    (rint) 1, (rint) 1, { (rint) -1 }
  };

  char buf[1024];
  char *line = fgets(buf, sizeof(buf), stdin);
  if (line == NULL) {
    return &EOF_ARRAY;
  }
  return c2rstring(line);
}

rint readchar()
{
  int ch = getchar();
  return (rint) ch;
}

rbool
strequal(rintarray *a, rintarray *b)
{
  return ristretto_array_equal((rarray *) a, (rarray *) b);
}

rintarray *
strappend(rintarray *a, rintarray* b)
{
  int na = a->length;
  int nb = b->length;
  rintarray *r = alloc_rintarray(na + nb);
  int j = 0;
  for (int i = 0; i < na; i++, j++) {
    r->data[j] = a->data[i];
  }
  for (int i = 0; i < nb; i++, j++) {
    r->data[j] = b->data[i];
  }
  return r;
}
