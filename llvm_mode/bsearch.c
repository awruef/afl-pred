#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

int mbsearch_it( int *arr, unsigned l, unsigned u, int val, int *found) {
  unsigned lu = u;
  unsigned ll = l;
  size_t   len = lu-ll;
  int      *larr = arr;

  while (len != 0) {
    size_t idx = len/2;
    int q = larr[idx] - val;
    if (q == 0) {
      *found = idx;
      return 0;
    }

    if (q > 0) {
      larr = &larr[0];
      lu = idx;
    } else {
      larr = &larr[idx];
      ll = idx;
    }

    len = lu-ll;
  }

  return -1;
}

int mbsearch_i( int *arr, unsigned l, unsigned u, int val, int *found) {
  size_t len = u-l;
  if (len == 0) {
    return -1;
  } else {
    size_t idx = len/2;
    int q = arr[idx] - val;

    if (q == 0) {
      *found = idx;
      return 0;
    } else {
      if (q > 0) 
        return mbsearch_i(&arr[0], l, idx, val, found);
      else 
        return mbsearch_i(&arr[idx], idx, u, val, found);
    }
  }
}

int mbsearch(int *arr, size_t len, int val, int *found) {
  return mbsearch_i(arr, 0, len, val, found);
}

int main(int argc, char *argv[]) {
  int bla[] = {2, 3, 8, 11};
  int r;
  int f;
  f = mbsearch(bla, 4, 2, &r);
  if (f == 0)
    printf("found at %d\n", r);
  else
    printf("not found\n");
  
  f = mbsearch(bla, 4, 8, &r);
  if (f == 0)
    printf("found at %d\n", r);
  else
    printf("not found\n");
  
  f = mbsearch(bla, 4, 21, &r);
  if (f == 0)
    printf("found at %d\n", r);
  else
    printf("not found\n");

  f = mbsearch(bla, 4, -21, &r);
  if (f == 0)
    printf("found at %d\n", r);
  else
    printf("not found\n");



  return 0;
}
