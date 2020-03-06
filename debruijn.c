#include <assert.h>
#include <errno.h>
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

/* Binomial coefficient */
/* fxtbook ch. 6, pp. 176-7 */
uint64_t choose(uint64_t n, uint64_t k) {
  if (k > n) {
    return 0;
  }
  if (k == 0 || k == n) {
    return 1;
  }
  uint64_t b = n - k + 1;
  uint64_t f = b;
  for (uint64_t j = 2; j <= k; j++) {
    ++f;
    b *= f;
    b /= j;
  }
  return b;
}

/* Determine the ordering of the given arrangement in lexical order */
uint64_t unrank(uint64_t x) {
  uint8_t b[64];      /* index of each set bit */
  uint8_t n = 0;
  uint8_t i;
  for (i = 0; i < 64; i++) {
    if (nth_bit(x, i)) {
      b[n++] = i;
    }
  }
  uint64_t rank = 0;
  for (i = 0; i < n; i++) {
    rank += choose(b[i], i + 1);
  }
  return rank;
}

const uint64_t mask[6] = {0x5555555555555555,
                          0x3333333333333333,
                          0x0f0f0f0f0f0f0f0f,
                          0x00ff00ff00ff00ff,
                          0x0000ffff0000ffff,
                          0x00000000ffffffff};

/* Swap consecutive groups of 2^b bits with their neighbors. For example, b=0
 * swaps bit 0 with bit 1, bit 2 with bit 3, etc.; b=3 swaps bits 0-7 with bits
 * 8-15, bits 16-23 with bits 24-31, etc. Equivalently, let each bit position in
 * a be swapped with the bit position gotten by swapping 0 and 1 in the bth
 * bit. */
/* depends on 2 colors */
/* doesn't depend on square */
uint64_t toggle_bit_position_a(uint64_t a, uint8_t b) {
  assert(b <= 6);
  const uint64_t bits = 1ULL << b;
  return ((a & mask[b]) << bits) | ((a & ~mask[b]) >> bits);
}

void toggle_bit_position_aa(uint64_t n_vertices, uint8_t aa[n_vertices], uint8_t b) {
  uint64_t i, j;
  uint8_t temp;
  const uint64_t bits = 1ULL << b;
  for (i = 0; i < n_vertices; i += 2 * bits) {
    for (j = i; j < i + bits; j++) {
      temp = aa[j];
      aa[j] = aa[j + bits];
      aa[j + bits] = temp;
    }
  }
}

/* depends on single value, no array version */
/* depends on 2 colors */
/* doesn't depend on square */
uint64_t swap_bit_positions_a(uint64_t a, uint8_t b0, uint8_t b1) {
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

void swap_bit_positions_aa(uint64_t n_vertices, uint8_t aa[n_vertices], uint8_t b0, uint8_t b1) {
  uint64_t i;
  uint8_t temp;
  assert(b0 < b1);
  /* TODO: could speed this up by not visiting all elements, only ones with b0'th bit 0 and b1'th bit 1 */
  for (i = 0; i < n_vertices; i++) {
    if (nth_bit(i, b0) == 0 && nth_bit(i, b1) == 1) {
      uint64_t ii = ((i | ~(1ULL << b1)) & (1ULL << b0));
      temp = aa[i];
      aa[ii] = aa[i];
      aa[i] = temp;
    }
  }
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
uint64_t choose_half(uint64_t n) {
  assert(n <= 66);  /* otherwise, result does not fit in a uint64_t */
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
  return d * (d-1) * (1ULL << (d-3));
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

void find_hypercube_colorings(uint8_t d, ToShow show, uint8_t global_count_any, uint8_t global_count_iso, uint64_t a, uint64_t coloring) {
  const uint64_t n_vertices = 1ULL << d;
  uint8_t * aa = malloc(n_vertices * sizeof(uint8_t));  /* hypercube coloring being checked */
  /* aa[n_vertices - 1] is most significant, aa[0] least significant */
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

  printf("Beginning of find_hypercube_colorings. a=0x%llx coloring=%llu\n", a, coloring);
  
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
      aa[i] = 1;
    }
    for (i = n_vertices / 2; i < n_vertices; i++) {
      aa[i] = 0;
    }
  }

  for (; coloring < n_colorings; coloring++) {
    assert(coloring == unrank(a));
    /* The hypercube has several automorphisms that enable us to save time; if
       we have a coloring and a transformation of the same coloring (say,
       with a reflection through one axis), we only need to check one of them.
       We're iterating in lexical order, so we can skip any coloring 'a' if the
       transformed version is less than 'a'. */

    if (!need_big_a) {
      /* Check for isomorphisms due to changing the names of colors. */
      /* depends on single value */
      /* doesn't depend on square */
      /* depends on 2 colors */
      if (~a < a) {
        goto skip;
      }
      /* Check the d isomorphisms formed by swapping bits in each of d
       * dimensions (that is, mirror reflection through any axis). */
      /* depends on single value */
      /* doesn't depend on square */
      /* depends on 2 colors */
      for (i = 0; i < d; i++) {
        if (toggle_bit_position_a(a, i) < a) {
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
            a_perm = swap_bit_positions_a(a_perm, 0, k);
          } else {
            a_perm = swap_bit_positions_a(a_perm, c[k], k);
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
    }
    
    /* Now count squares. */
    for (i = 0; i < 16; i++) {
      c_any[i] = 0;
    }
    for (i = 0; i < 6; i++) {
      c_iso[i] = 0;
    }
    uint8_t count_any = global_count_any;
    uint8_t count_iso = global_count_iso;

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
          if (count_any) {
            c_any[square]++;
          }
          if (count_iso) {
            c_iso[coloring_bin[square]]++;
          }

          /* We can stop early if we already have too many in any bin. */
          if (show == SHOW_STRICT) {
            if (count_any && c_any[square] > perfect_per_bin_any) {
              count_any = 0;
            }
            if (count_iso && c_iso[coloring_bin[square]] > perfect_per_bin_iso) {
              count_iso = 0;
            }
            if (!count_any && !count_iso) {
              goto skip;
            }
          }
          
          /* increment n, ignoring bit positions di and dj */
          /* (Knuth 7.1.3, p150) */
          const uint64_t dmask = ~((1ULL << di) | (1ULL << dj));
          n = ((n - dmask) & dmask);
        }
      }
    }

    /* depends on square */
    /* doesn't depend on single value (decides whether single value) */
    /* doesn't depend on 2 colors */
    if (global_count_any && is_interesting_coloring(show, 16, c_any)) {
      printf("any orientation:\t");
      if (need_big_a) {
        print_coloring_aa(n_vertices, aa, 16, c_any);
      } else {
        print_coloring_a(n_vertices, a, 16, c_any);
      }
      fflush(stdout);
    }
    if (global_count_iso && is_interesting_coloring(show, 6, c_iso)) {
      printf("up to isomorphism:\t");
      if (need_big_a) {
        print_coloring_aa(n_vertices, aa, 6, c_iso);
      } else {
        print_coloring_a(n_vertices, a, 6, c_iso);
      }
      fflush(stdout);
    }
    
    /* set a to the next combination and terminate if done */
    /* depends on 2 colors */
    /* doesn't depend on square */
    /* depends on single value */
  skip:
    if (need_big_a) {
      uint64_t p, q;
      /* start rightmost, search left, find location p of rightmost 1 */
      for (i = 0; i < n_vertices; i++) {
        if (aa[i] == 1) {
          break;
        }
      }
      p = i;
      assert(p != n_vertices);  /* array contains no 1s ?! */
      /* find location q of first 0 left of p */
      for (; i < n_vertices; i++) {
        if (aa[i] == 0) {
          break;
        }
      }
      q = i;
      if (q == n_vertices) {  /* last combination; we're done */
        break;
      }
      /* at q and q - 1: 01 -> 10 */
      aa[q] = 1;
      aa[q - 1] = 0;
      uint64_t min, max;
      if (p < q - p - 1) {
        min = p;
        max = q - p - 1;
      } else {
        min = q - p - 1;
        max = p;
      }
      /* in rightmost q - 1 bits, shift q - p - 1 ones to rightpost position */
      for (i = 0; i < min; i++) {
        aa[i] = 1;
      }
      for (i = max; i < q - 1; i++) {
        aa[i] = 0;
      }
    } else {
      /* Gosper's hack */
      uint64_t y = a & -a;  /* rightmost set bit of a, call it position p */
      uint64_t z = a + y;   /* increment left of p: 0 followed by 1s -> 1 followed by 0s */
      if ((n_vertices == 64 && z == 0) || z == (1ULL << n_vertices)) {
        break;
      }
      /* a ^ z = select 1s that need to be shifted right */
      /* >> 2 / y: shift the 1s (2 + log_2 y) right */
      /* | z: combine with incremented bits left of p */
      a = (((a ^ z) >> 2) / y) | z;
    }

    /* print progress */
    /* no dependences */
    if (coloring == milestone) {
      printf("%f%% a=0x%016llx coloring=%llu/%llu\n", (double)coloring * 100 / n_colorings, a, coloring, n_colorings);
      fflush(stdout);
      milestone += milestone_interval;
    }
  }
  free(aa);
}

/* depends on square */
/* depends on 2 colors */
/* doesn't depend on single value */
int main(int argc, char *argv[]) {
  if (argc < 4) {
    fprintf(stderr, "What?\n");
    exit(1);
  }
  char * end;
  unsigned long d_big = strtoul(argv[1], &end, 0);
  if (end[0] != '\0') {
    fprintf(stderr, "I don't understand the first argument d (%lu)\n", d_big);
    exit(1);
  }
  if (d_big > 6) {
    fprintf(stderr, "The first argument d is too big (max 6)\n");
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
    fprintf(stderr, "I don't understand the second argument: must be 'all', 'strict', or '2'\n");
    exit(1);
  }
  uint8_t global_count_any, global_count_iso;
  if (strcmp(argv[3], "any") == 0) {
    global_count_any = 1;
    global_count_iso = 0;
  } else if (strcmp(argv[3], "iso") == 0) {
    global_count_any = 0;
    global_count_iso = 1;
  } else if (strcmp(argv[3], "both") == 0) {
    global_count_any = 1;
    global_count_iso = 1;
  } else {
    fprintf(stderr, "I don't understand the third argument: must be 'any', 'iso', or 'both'\n");
    exit(1);
  }
  uint64_t a = (1ULL << (1ULL << (d - 1))) - 1;
  uint64_t coloring = 0;
  if (argc == 5) {
    fprintf(stderr, "I see a fourth argument 'a' but not a fifth argument 'coloring'\n");
  } else if (argc == 6) {
    uintmax_t a_big = strtoumax(argv[4], &end, 0);
    if (end[0] != '\0' || a_big > UINT64_MAX) {
      fprintf(stderr, "I don't understand the fourth argument a\n");
      exit(1);
    }
    if (a_big > UINT64_MAX || errno == ERANGE) {
      fprintf(stderr, "The fourth argument 'a' is too big\n");
      exit(1);
    }
    a = (uint64_t)a_big;
    uintmax_t coloring_big = strtoumax(argv[5], &end, 0);
    if (end[0] != '\0') {
      fprintf(stderr, "I don't understand the fifth argument 'coloring'.\n");
      exit(1);
    }
    if (coloring_big > UINT64_MAX || errno == ERANGE) {
      fprintf(stderr, "The fifth argument 'coloring' is too big.\n");
      exit(1);
    }
    coloring = (uint64_t)coloring_big;
  }
  find_hypercube_colorings(d, show, global_count_any, global_count_iso, a, coloring);
  return 0;
}
