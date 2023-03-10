#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

#define MINSIZE 16 // Minimalny rozmiar bloku (4 bloki 4 bajtowe)
#define WORDSIZE sizeof(word_t)

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = (size | flags);
  word_t *btft = bt_footer(bt);
  *btft = (size | flags);
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  return (void *)bt + bt_size(bt);
}

/* Returns address of previous block. */
static inline word_t *bt_prev(word_t *bt) {
  return (void *)bt - bt_size((void *)bt - sizeof(word_t));
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  size_t alsize = round_up(size + 2 * WORDSIZE);
  return alsize;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}
/* --=[ coaelesce ]=----------------------------------------------------------
 */
static void *coaelesce(word_t *bt) {
  word_t *prevblock = bt_prev(bt);
  word_t *nextblock = bt_next(bt);
  size_t prevsize = bt_size(prevblock);
  size_t nextsize = bt_size(nextblock);
  size_t size = bt_size(bt);
  if (bt_used(prevblock) && bt_used(nextblock)) {
    return bt;
  } else if (bt_used(prevblock) && bt_free(nextblock)) {
    size += nextsize;
    bt_make(bt, size, FREE);
  } else if (bt_free(prevblock) && bt_used(nextblock)) {
    size += prevsize;
    bt_make(prevblock, size, FREE);
    bt = prevblock;
  } else {
    size += prevsize + nextsize;
    bt_make(prevblock, size, FREE);
    bt = prevblock;
  }
  return bt;
}

/* --=[ mm_extend_heap
 * ]=---------------------------------------------------------- */
/*Rozszerzanie stery*/
static void *mm_extend_heap(size_t words) {
  word_t *bt;
  word_t *newep;
  void *ptr;
  /* Rozszerzamy o ilość bloków które są wielokrotnością 16 by zachować
   * alignment*/
  size_t alsize = round_up(words) * WORDSIZE;
  ptr = mem_sbrk(alsize);
  if (ptr == (void *)-1) {
    return NULL;
  }
  bt = bt_fromptr(ptr);
  bt_make(bt, alsize, FREE);
  newep = bt_next(bt);
  *(word_t *)newep = 0 | USED;

  return coaelesce(bt);
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  void *ptr = morecore(2 * MINSIZE);
  memset(ptr, 0, 12);
  bt_make((ptr + 3 * WORDSIZE), MINSIZE, USED);
  memset((ptr + 4 * WORDSIZE), 0, 8);
  void *epilogue = (ptr + 7 * WORDSIZE);
  *(word_t *)epilogue = 0 | USED;
  heap_start = mm_extend_heap(mem_pagesize() / WORDSIZE);
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t *bt = heap_start;
  while (!(bt_size(bt) == 0 && bt_used(bt))) {
    if (bt_free(bt) && bt_size(bt) >= reqsz) {
      return bt;
    }
    bt = bt_next(bt);
  }
  return NULL;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
}
#endif
/*Ustawiamy znaleziony wolny blok na zajęty i w razie potrzeby dzielimy go*/
static void createblock(size_t size, word_t *bt) {
  size_t oldsize = bt_size(bt);
  bt_make(bt, size, USED);
  /*Jeżeli wolny blok był większy niż potrzebny rozmiar rozdzielamy go*/
  if (oldsize > size) {
    bt_make(bt_next(bt), oldsize - size, FREE);
  }
}

void *malloc(size_t size) {
  size_t alsize;
  size_t extend_size;
  word_t *bt;
  if (size == 0) {
    return NULL;
  }
  alsize = blksz(size);
  bt = find_fit(alsize);
  if (bt != NULL) {
    createblock(alsize, bt);
    return bt_payload(bt);
  } else {
    /*Żeby zredukować liczbę syscalli do jądra nawet jeżeli będziemy
     * potrzebowali tylko dodatkowej małej ilości pamięci poprosimy go o całą
     * stronę*/
    extend_size = (alsize > mem_pagesize()) ? alsize : mem_pagesize();
    bt = mm_extend_heap(extend_size);
    if (bt == NULL) {
      return NULL;
    }
    createblock(alsize, bt);
    return bt_payload(bt);
  }
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr == NULL) {
    return NULL;
  }
  word_t *bt = bt_fromptr(ptr);
  size_t size = bt_size(bt);
  bt_make(bt, size, FREE);
  coaelesce(bt);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  if (old_ptr == NULL) {
    return malloc(size);
  }
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }
  word_t *old_bt = bt_fromptr(old_ptr);
  size_t alsize = blksz(size);
  size_t old_size = bt_size(old_bt);
  /*Rozmiary bloków takie same. Nic nie robimy*/
  if (alsize == old_size) {
    return old_ptr;
  }
  if (alsize < old_size) {
    /*Sprawdzamy czy możemy podzielić blok na dwa mniejsze kawałki by zadowolić
     * wymagania*/
    if (alsize >= MINSIZE && (old_size - alsize) >= MINSIZE) {
      bt_make(old_bt, alsize, USED);
      word_t *nextbt = bt_next(old_bt);
      bt_make(nextbt, (old_size - alsize), USED);
      free(bt_payload(nextbt));
      return old_ptr;
    }
    word_t *newbt = malloc(size);
    if (newbt == NULL) {
      return NULL;
    }
    memcpy(bt_payload(newbt), old_ptr, size);
    free(old_ptr);
    return bt_payload(newbt);
  } else {
    word_t *newbt = malloc(size);
    if (newbt == NULL) {
      return NULL;
    }
    memcpy(bt_payload(newbt), old_ptr, size);
    free(old_ptr);
    return bt_payload(newbt);
  }
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
}
