#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* value of the nth bit of x */
/* no dependences */
uint8_t nth_bit(uint64_t x, uint8_t n) {
  return (x & (1ULL << n)) >> n;
}

/* only for 64-bit, no array version */
/* depends on 2 colors */
void print_binary(uint8_t n, uint64_t a) {
  uint8_t i = n;
  do {
    printf("%hhu", nth_bit(a, --i));
  } while (i != 0);
}

/* no dependences */
void print_coloring_aa(uint64_t n_aa, uint8_t aa[n_aa],
                       uint64_t n_c, uint64_t c[n_c]) {
  uint64_t i;

  i = n_aa;
  do {
    printf("%hhu", aa[--i]);
  } while (i != 0);
  printf("\t");
  for (i = 0; i < n_c; i++) {
    printf("%llu ", c[i]);
  }
  printf("\n");
}

/* no dependences */
void print_coloring_a(uint64_t n_a, uint64_t a,
                      uint64_t n_c, uint64_t c[n_c]) {
  uint64_t i;
  print_binary(n_a, a);
  printf("\t");
  for (i = 0; i < n_c; i++) {
    printf("%llu ", c[i]);
  }
  printf("\n");
}

const uint64_t mask[6] = {0x5555555555555555,
                          0x3333333333333333,
                          0x0f0f0f0f0f0f0f0f,
                          0x00ff00ff00ff00ff,
                          0x0000ffff0000ffff,
                          0x00000000ffffffff};

/* Swap consecutive groups of 2^b bits with their neighbors. For example, b=0
 * swaps bit 0 with bit 1, bit 2 with bit 3, etc.; b=3 sways bits 0-7 with bits
 * 8-15, bits 16-23 with bits 24-31, etc. Equivalently, let each bit position in
 * a be swapped with the bit position gotten by swapping 0 and 1 in the bth
 * bit. */
/* depends on single value, no array version */
/* depends on 2 colors */
/* doesn't depend on square */
uint64_t toggle_bit_position(uint64_t a, uint8_t b) {
  assert(b <= 6);
  const uint64_t bits = 1 << b;
  return ((a & mask[b]) << bits) | ((a & ~mask[b]) >> bits);
}

/* depends on single value, no array version */
/* depends on 2 colors */
/* doesn't depend on square */
uint64_t swap_bit_positions(uint64_t a, uint8_t b0, uint8_t b1) {
  assert(b0 <= 6);
  assert(b1 <= 6);
  assert(b0 < b1);
  const uint64_t mask0 = ~mask[b0] & mask[b1]; /* b0th bit 0, b1th bit 1 */
  const uint64_t mask1 = mask[b0] & ~mask[b1]; /* b0th bit 1, b0th bit 0 */
  uint8_t shift = (1 << b1) - (1 << b0);
  return (((a & mask0) << shift) |
          ((a & mask1) >> shift) |
          (a & ~mask0 & ~mask1));
}

/* no dependences */
typedef enum {
  SHOW_ALL,     /* print all colorings */
  SHOW_STRICT,  /* print only if colorings are exactly equal */
  SHOW_2,       /* print if number of distinct numbers of colorings is 1 or 2 */
} ToShow;

/* Index is a 4-bit number representing a two-color coloring of the vertices of
 * a square (listed in clockwise or counterclockwise order). Categorize each as
 * one of the 6 possible colorings. */
/* depends on square; no non-square versions */
/* depends on 2 colors */
const uint8_t coloring_bin[16] = {0,  /* 0000 */
                                  1,  /* 0001 */
                                  1,  /* 0010 */
                                  2,  /* 0011 */
                                  1,  /* 0100 */
                                  3,  /* 0101 */
                                  2,  /* 0110 */
                                  4,  /* 0111 */
                                  1,  /* 1000 */
                                  2,  /* 1001 */
                                  3,  /* 1010 */
                                  4,  /* 1011 */
                                  2,  /* 1100 */
                                  4,  /* 1101 */
                                  4,  /* 1110 */
                                  5}; /* 1111 */

/* n choose n/2 */
/* doesn't depend on single value, but d must be <= 64 */
/* depends on 2 colors */
/* TODO: What values of n cause overflow? */
uint64_t choose_half(uint64_t n) {
  uint64_t x = 1;
  uint64_t i;
  for (i = 0; i < n/2; i++) {
    x *= n - i;
    x /= i + 1;
  }
  return x;
}

/* number of subsquares (2-dimensional subhypercubes) of a d-dimensional
 * hypercube */
/* depends on square */
/* doesn't depend on colors */
uint64_t hypercube_squares(uint8_t d) {
  if (d < 2) return 0;
  if (d == 2) return 1;
  return d * (d-1) * (1 << (d-3));
}

/* The number of distinct values in the array x with length n */
/* no dependences */
uint64_t distinct_values(uint64_t n, uint64_t x[n]) {
  uint64_t i, j;
  uint8_t eq[n];          /* 1 if corresponding element of c is equal to
                           * some element of c with a smaller index */
  uint64_t distinct_values = n;
  
  for (i = 0; i < n; i++) {
    eq[i] = 0;
  }
  for (i = 0; i < n - 1; i++) {
    for (j = i + 1; j < n; j++) {
      if (!eq[j] && x[i] == x[j]) {
        eq[j] = 1;
        distinct_values--;
      }
    }
  }
  return distinct_values;
}

/* whether all n values in the array x are the same */
/* no dependences */
uint8_t all_same(uint64_t n, uint64_t x[n]) {
  uint64_t i;

  for (i = 1; i < n; i++) {
    if (x[0] != x[i]) return 0;
  }
  return 1;
}

/* no dependences */
uint8_t is_interesting_coloring(ToShow show, uint64_t n, uint64_t x[n]) {
  if (show == SHOW_ALL) {
    return 1;
  } else if (show == SHOW_STRICT) {
    return all_same(n, x);
  } else if (show == SHOW_2) {
    return (distinct_values(n, x) <= 2);
  }
  fprintf(stderr, "Error: weird value of \"show\"\n");
  exit(1);
}

void find_hypercube_colorings(uint8_t d, ToShow show, uint64_t a, uint64_t coloring) {
  const uint64_t n_vertices = 1<<d;
  uint8_t aa[n_vertices];  /* hypercube coloring being checked */
  uint8_t square;         /* square coloring being checked */
  uint64_t c_any[16];     /* count squares of each of 16 possible colorings */
  uint64_t c_iso[6];      /* count squares of each of 6 possible colorings up to
                           * isomorphism */
  uint64_t n;             /* least vertex of current square; 'di'th and 'dj'th
                           * bit of n determine which vertex of the square */
  uint8_t di, dj, dk;
  uint64_t i;

  /* used in Heap's algorithm to generate permutations */
  uint8_t p[d];
  uint8_t p_temp;
  uint64_t a_perm;
  uint8_t c[d+1];

  printf("Beginning of find_hypercube_colorings. a=%llx coloring=%llu\n", a, coloring);
  
  /* if n_vertices is small enough, 'a' will fit in a uint64_t;
   * otherwise use an array */
  /* depends on 2 colors */
  const uint8_t need_big_a = (n_vertices > 64);
  
  /* number of colorings to check */
  const uint64_t n_colorings = choose_half(n_vertices);
  uint64_t milestone_interval = 1ULL << 30;  /* print progress regularly */
  uint64_t milestone = coloring + milestone_interval;
  
  /* number of colorings in each bin if it were a perfect de Bruijn coloring */
  /* depends on square */
  /* depends on 2 colors */
  uint64_t perfect_per_bin_any = hypercube_squares(d) / 16;
  uint64_t perfect_per_bin_iso = hypercube_squares(d) / 6;
  if (show == SHOW_STRICT) {
    if (hypercube_squares(d) % 16 != 0) {
      printf("Note: no de Bruijn coloring will be found for the 16 square colorings because the number of squares (%llu) is not divisible by 16.\n", hypercube_squares(d));
    }
    if (hypercube_squares(d) % 6 != 0) {
      printf("Note: no de Bruijn coloring will be found for the 6 square colorings up to isomorphism because the number of squares (%llu) is not divisible by 6.\n", hypercube_squares(d));
    }
  }
  
  /* initialize a */
  /* depends on 2 colors */
  /* doesn't depend on square */
  if (need_big_a) {
    for (i = 0; i < n_vertices / 2; i++) {
      aa[i] = 0;
    }
    for (i = n_vertices / 2; i < n_vertices; i++) {
      aa[i] = 1;
    }
  }

  for (; coloring < n_colorings; coloring++) {
    /* The hypercube has d isomorphisms formed by swapping bits in each of d
     * dimensions. There's no need to check both a pattern 'a' and its
     * bit-swapped version. Check for duplicates. */
    /* depends on single value */
    /* doesn't depend on square */
    /* depends on 2 colors */
    for (i = 0; i < d; i++) {
      if (toggle_bit_position(a, i) < a) {
        goto skip;
      }
    }
    /* Check for duplicates due to axis permutations. Use Heap's algorithm to
     * iterate through all axis permutations using swaps */
    /* doesn't depend on square */
    /* depends on 2 colors */
    a_perm = a;
    for (i = 0; i < d+1; i++) {
      c[i] = 0;
    }
    uint8_t k = 0;
    
    while (k < d) {
      if (c[k] < k) {
        if ((k & 1) == 0) {
          a_perm = swap_bit_positions(a_perm, 0, k);
        } else {
          a_perm = swap_bit_positions(a_perm, c[k], k);
        }
        if (a_perm < a) {
          goto skip;
        }
        c[k]++;
        k = 0;
      } else {
        c[k] = 0;
        k++;
      }
    }
    
    for (i = 0; i < 16; i++) {
      c_any[i] = 0;
    }
    for (i = 0; i < 6; i++) {
      c_iso[i] = 0;
    }

    /* for each square indicated by bit positions di and dj */
    /* depends on square */
    /* depends on 2 colors */
    for (di = 0; di < d - 1; di++) {
      for (dj = di + 1; dj < d; dj++) {
        n = 0;
        while (n != n_vertices) {
          if (need_big_a) {
            square =
              (aa[n] << 3) |                          /* 00 */
              (aa[n | (1 << di)] << 2) |              /* 01 */
              (aa[n | (1 << di) | (1 << dj)] << 1) |  /* 11 */
               aa[n | (1 << dj)];                     /* 10 */
          } else {
            square =
              nth_bit(a, n) << 3 |
              nth_bit(a, n | (1 << di)) << 2 |
              nth_bit(a, n | (1 << di) | (1 << dj)) << 1 |
              nth_bit(a, n | (1 << dj));
          }
          c_any[square]++;
          c_iso[coloring_bin[square]]++;

          /* We can stop early if we already have too many in any bin. */
          if (show == SHOW_STRICT &&
              (c_any[square] > perfect_per_bin_any ||
               c_iso[coloring_bin[square]] > perfect_per_bin_iso)) {
            goto skip;
          }
          
          /* increment n, ignoring bit positions di and dj */
          for (dk = 0; dk < d + 1; dk++) {
            if (dk == di || dk == dj) continue;
            if ((n & (1 << dk)) == 0) {
              n = (n | (1 << dk));
              break;
            }
            n = (n & ~(1 << dk));
          }
        }
      }
    }

    /* depends on square */
    /* doesn't depend on single value (decides whether single value) */
    /* doesn't depend on 2 colors */
    if (is_interesting_coloring(show, 16, c_any)) {
      printf("any orientation:\t");
      if (need_big_a) {
        print_coloring_aa(n_vertices, aa, 16, c_any);
      } else {
        print_coloring_a(n_vertices, a, 16, c_any);
      }
    }
    if (is_interesting_coloring(show, 6, c_iso)) {
      printf("up to isomorphism:\t");
      if (need_big_a) {
        print_coloring_aa(n_vertices, aa, 6, c_iso);
      } else {
        print_coloring_a(n_vertices, a, 6, c_iso);
      }
    }
    
    /* set a to the next combination and terminate if done */
    /* depends on 2 colors */
    /* doesn't depend on square */
    /* depends on single value */
  skip:
    if (need_big_a) {
      fprintf(stderr, "Error: I don't know how to move to the next combination for arrays yet\n");
      exit(1);
    } else {
      /* Gosper's hack */
      uint64_t y = a & -a;  /* rightmost set bit of a, call it position p */
      uint64_t z = a + y;   /* +1 to bits left of p */
      if ((n_vertices == 64 && z == 0) || z == (1 << n_vertices)) {
        break;
      }
      /* a ^ z = 0s for bits unchanged by the +1, 1s changed, 0 p and after */
      /* >> 2: now 0s, 1s up to p and p-1, 0s after */
      /* / y: ? */
      /* | z */
      a = (((a ^ z) >> 2) / y) | z;
    }

    /* print progress */
    /* no dependences */
    if (coloring == milestone) {
      printf("%f%% a=0x%016llx coloring=%llu/%llu\n", (double)coloring * 100 / n_colorings, a, coloring, n_colorings);
      milestone += milestone_interval;
    }
  }
}

/* depends on square */
/* depends on 2 colors */
/* doesn't depend on single value */
int main(int argc, char *argv[]) {
  if (argc < 2) {
    fprintf(stderr, "What?");
    exit(1);
  }
  char * end;
  unsigned long d_big = strtoul(argv[1], &end, 0);
  if (end[0] != '\0' || d_big > UINT8_MAX) {
    fprintf(stderr, "I don't understand the first argument d (%lu)\n", d_big);
    exit(1);
  }
  uint8_t d = (uint8_t)d_big;
  ToShow show;
  if (strcmp(argv[2], "all") == 0) {
    show = SHOW_ALL;
  } else if (strcmp(argv[2], "strict") == 0) {
    show = SHOW_STRICT;
  } else if (strcmp(argv[2], "2") == 0) {
    show = SHOW_2;
  } else {
    fprintf(stderr, "I don't understand the second argument: all, strict, or 2\n");
    exit(1);
  }
  uint64_t a = (1ULL << 32) - 1;
  uint64_t coloring = 0;
  if (argc == 4) {
    fprintf(stderr, "I see a third argument 'a' but not a fourth argument 'coloring'\n");
  } else if (argc == 5) {
    uintmax_t a_big = strtoumax(argv[3], &end, 0);
    if (end[0] != '\0' || a_big > UINT64_MAX) {
      fprintf(stderr, "I don't understand the third argument a\n");
      exit(1);
    }
    a = (uint64_t)a_big;
    uintmax_t coloring_big = strtoumax(argv[4], &end, 0);
    if (end[0] != '\0' || coloring_big > UINT64_MAX) {
      fprintf(stderr, "I don't understand the fourth argument 'coloring.'\n");
      exit(1);
    }
    coloring = (uint64_t)coloring_big;
  }
  find_hypercube_colorings(d, show, a, coloring);
  return 0;
}
