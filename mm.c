// Mateusz Marszałek 323941
/*Oświadczam że jestem jedynym autorem kodu źródłowego*/
/* OPIS
Poniższy alokator przydziela pamięc korzystając z drzew splay.
Dodatkowo zrobiona jest optymalizacja boundary tag i skrócenie adresów
do 4 bajtów korzystając z fakty że mamy nie więcej niż 4Gib=2^32 bajtów pamięci
na stercie. Pierwsza i najprostsza wersja przechodząca testy była bazowana na
CSAPP (oczywiście z modyfikacją alignmentu z 8 do 16).
Opis drzew splay
Implementując drzewa splay posłużyłem się linkiem podanym w opisie projektu
(www.link.cs.cmu.edu/link/ftp-site/splaying/top-down-splay.c)
Dwa oczywiste wyzwania jakie stoi przy implementacji drzew splay to
a) przerobienie kodu tak żeby zamiast struktur używał tylko wskaźników.
Najtrudniejszą częścią tego jest rozwiązanie tego gdzie powinno znajdować się
"N" wykorzystywane w procedurze splay. Ja zdecydowałem że wykorzystam do tego
nasz padding dodawany w procedurze mm_init (padding ma 3 bloki więc idealnie się
do tego nada) b) Drzewa splay nie dodają duplikatów, my chcemy jednak żeby takie
duplikaty znalazły się w drzewie splay (możemy mieć kilka bloków takiego samego
rozmiaru). Można to rozwiązać na dwa sposoby. Pierwszy (którego przyznaję się że
nie testowałęm gdyż drugi wydawał mi się znacznie lepszy) to trzymanie
dodatkowego wskaźnika w wolnym bloku który będzie wskazywał na kolejny wolny
blok tego samego rozmiaru. Wtedy w drzewie splay zamiast bloków trzymamy tak
naprawdę listę wolnych bloków. Oczywistym minusem jest to że wtedy potrzebujemy
minimum trzech bloków do trzymania trzech wskaźników przez co minimalny rozmiar
bloku podskoczy nam do 32. Drugie rozwiązanie to żeby porównywać bloki w drzewie
splay nie tylko po rozmiarach ale także po adresach. Kiedy bloki mają taki sam
rozmiar to kontynuujemy porówywanie ich po adresach. Zalętą jest to że nie
zwiększamy minimalnego rozmiaru.
Opis bloku:
Wolny
|HEADER|ADRES LEWEGO SYNA|ADRES PRAWEGO SYNA|PADDING|FOOTER|
Zajęty
|HEADER|PAYLOAD|PADDING(opcjonalny)|
Wkładanie bloku (insert)
Wykonujemy splay żeby przesunąć blok który znaleźlibyśmy tuż przed dotarciem do
wstawianego bloku (gdyby znajdował się on w drzewie) a następnie w zależności od
tego czy node jest większy czy mniejszy według naszego komparatora(najpierw
porównujemy po rozmiarze, a gdy są one równe to po adresach) podpinamy
odpowiednie części starego drzewa pod lewego i prawego syna naszego nowego bloku
który tym samym zostaje nowym korzeniem
Usuwanie bloku (delete)
Używamy splay by przesunąć usuwany blok do korzenia a następnie tworzym z lewego
i prawego syna nowe drzewo. Jeżeli nie ma lewego poddrzewa to nowym drzewem jest
prawe poddrzewo w przeciwnym wypadku robimy splay dla wartości takich jak miał
usunięty blok tylko w lewym poddrzewie, a następnie podpinamy pod prawe
poddrzewo lewego poddrzewa (które musi być teraz puste) prawe poddrzewo starego
drzewa
Przydział bloku
Znajdujemy blok wykonując zwykłe przeszukiwanie drzewa (jeżeli aktualnie
rozpatrywany rozmiar node jest mniejszy niż wymagany to idziemy do prawego syna
w przeciwnym wypadku do lewego) i zwracamy najlepszego kandydata albo NULL.
Następnie przy zamienianiu bloku z wolnego na zajęty sprawdzamy czy możemy go
podzielić, jeżeli jest większy niż to co potrzebujemy. Zwalnianie bloku
Zamieniamy blok na free przez bt_make, a następnie wywołujemy coalesce. Potem
nasz nowy wolny blok dodajemy do drzewa procedurą insert
 */
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
//#define DEBUG
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

// static word_t *heap_start; /* Address of the first block */
static word_t *free_list_start; /*Korzeń drzewa*/
static word_t *free_list_end;
static word_t *heap_start; /*Wskaźnik na prolog*/
static void *heap_lo_addr;

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

static inline void bt_make_opt(word_t *bt, size_t size, bt_flags flags) {
  *bt = (size | flags);
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

static inline void bt_set_l_ptr(word_t *bt, word_t *ptr) {
  *(bt + 1) = ((uintptr_t)ptr - (uintptr_t)heap_lo_addr) & 0xffffffff;
}

static inline void bt_set_r_ptr(word_t *bt, word_t *ptr) {
  *(bt + 2) = ((uintptr_t)ptr - (uintptr_t)heap_lo_addr) & 0xffffffff;
}

static inline word_t *bt_get_l_ptr(word_t *bt) {
  if (*(bt + 1) == 0) {
    return NULL;
  }
  return heap_lo_addr + *(bt + 1);
}
static inline word_t *bt_get_r_ptr(word_t *bt) {
  if (*(bt + 2) == 0) {
    return NULL;
  }
  return heap_lo_addr + *(bt + 2);
}

static inline int cmp_blocks_l(size_t size, uintptr_t bt, word_t *ptr) {
  if (size == bt_size(ptr)) {
    return (word_t *)bt < ptr;
  }
  return size < bt_size(ptr);
}

static inline int cmp_blocks_g(size_t size, uintptr_t bt, word_t *ptr) {
  if (size == bt_size(ptr)) {
    return (word_t *)bt > ptr;
  }
  return size > bt_size(ptr);
}
/* --=[ splay tree ]=----------------------------------------------------------
 */
/*www.link.cs.cmu.edu/link/ftp-site/splaying/top-down-splay.c*/

/*Splay przesuwa do korzenia wierzchołek o podanym rozmiarze i adresie.
Jeżeli nie ma go w drzewie do korzenia jest przesuwany ostatni wierzchołek na
jaki natrafimy prze NULL (gdyby ten wierzchołek jednak był w drzewie)*/
static word_t *splay(size_t size, uintptr_t bt, word_t *t) {
  word_t *N = heap_lo_addr;
  bt_set_l_ptr(N, NULL);
  bt_set_r_ptr(N, NULL);
  if (t == NULL)
    return t;
  word_t *l = N;
  word_t *r = N;
  word_t *y;
  for (;;) {
    if (cmp_blocks_l(size, bt, t)) {
      if (bt_get_l_ptr(t) == NULL)
        break;
      if (cmp_blocks_l(size, bt, bt_get_l_ptr(t))) {
        y = bt_get_l_ptr(t);
        bt_set_l_ptr(t, bt_get_r_ptr(y));
        bt_set_r_ptr(y, t);
        t = y;
        if (bt_get_l_ptr(t) == NULL)
          break;
      }
      bt_set_l_ptr(r, t);
      r = t;
      t = bt_get_l_ptr(t);
    } else if (cmp_blocks_g(size, bt, t)) {
      if (bt_get_r_ptr(t) == NULL)
        break;
      if (cmp_blocks_g(size, bt, bt_get_r_ptr(t))) {
        y = bt_get_r_ptr(t);
        bt_set_r_ptr(t, bt_get_l_ptr(y));
        bt_set_l_ptr(y, t);
        t = y;
        if (bt_get_r_ptr(t) == NULL)
          break;
      }
      bt_set_r_ptr(l, t);
      l = t;
      t = bt_get_r_ptr(t);
    } else {
      break;
    }
  }
  bt_set_r_ptr(l, bt_get_l_ptr(t));
  bt_set_l_ptr(r, bt_get_r_ptr(t));
  bt_set_l_ptr(t, bt_get_r_ptr(N));
  bt_set_r_ptr(t, bt_get_l_ptr(N));
  return t;
}
/*Wkładamy do drzewa blok bt.*/
static word_t *insert(word_t *bt, word_t *t) {
  if (t == NULL) {
    bt_set_l_ptr(bt, NULL);
    bt_set_r_ptr(bt, NULL);
    return bt;
  }
  t = splay(bt_size(bt), (uintptr_t)bt, t);
  if (cmp_blocks_l(bt_size(bt), (uintptr_t)bt, t)) {
    bt_set_l_ptr(bt, bt_get_l_ptr(t));
    bt_set_r_ptr(bt, t);
    bt_set_l_ptr(t, NULL);
    return bt;
  } else if (cmp_blocks_g(bt_size(bt), (uintptr_t)bt, t)) {
    bt_set_r_ptr(bt, bt_get_r_ptr(t));
    bt_set_l_ptr(bt, t);
    bt_set_r_ptr(t, NULL);
    return bt;
  } else {
    return t;
  }
}
/*Usuwamy blok z drzewa*/
static word_t *delete (word_t *bt, word_t *t) {
  word_t *x;
  if (t == NULL)
    return NULL;
  t = splay(bt_size(bt), (uintptr_t)bt, t);
  if (bt == t) {
    if (bt_get_l_ptr(t) == NULL) {
      x = bt_get_r_ptr(t);
    } else {
      x = splay(bt_size(bt), (uintptr_t)bt, bt_get_l_ptr(t));
      bt_set_r_ptr(x, bt_get_r_ptr(t));
    }
    return x;
  }
  return t;
}
/* --=[ funkje pomocnicze
 * ]=----------------------------------------------------------
 */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  size_t alsize = round_up(size + WORDSIZE);
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
  bt_flags prevfr = bt_get_prevfree(bt);
  word_t *nextblock = bt_next(bt);
  size_t size = bt_size(bt);
  if (bt_free(nextblock)) {
    size += bt_size(nextblock);
    free_list_start = delete (nextblock, free_list_start);
  }
  if (prevfr) {
    bt = bt_prev(bt);
    size += bt_size(bt);
    prevfr = bt_get_prevfree(bt);
    free_list_start = delete (bt, free_list_start);
  }
  bt_make(bt, size, (prevfr | FREE));
  return bt;
}

/* --=[ mm_extend_heap * ]=-----------------------------------------------------
 */
/*Rozszerzanie stery*/
static void *mm_extend_heap(size_t size) {
  word_t *bt;
  word_t *newep;
  void *ptr;
  ptr = mem_sbrk(size);
  if (ptr == (void *)-1) {
    return NULL;
  }
  bt = bt_fromptr(ptr);
  bt_flags prevfr = bt_get_prevfree(bt);
  bt_make(bt, size, (prevfr | FREE));
  newep = bt_next(bt);
  *(word_t *)newep = 0 | (PREVFREE | USED);

  return bt = coaelesce(bt);
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  free_list_start = NULL;
  free_list_end = NULL;
  void *ptr = morecore(2 * MINSIZE);
  heap_lo_addr = mem_heap_lo();
  heap_start = ptr + 3 * WORDSIZE;
  bt_make((ptr + 3 * WORDSIZE), MINSIZE, USED);
  void *epilogue = (ptr + 7 * WORDSIZE);
  *(word_t *)epilogue = 0 | USED;
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* splay tree best fit. */
static word_t *find_fit(size_t reqsz) {
  word_t *bt = free_list_start;
  word_t *best = NULL;
  size_t best_s = 0;
  while (bt) {
    if (bt_size(bt) >= reqsz) {
      if (best == NULL && bt_size(bt) >= reqsz) {
        best = bt;
        best_s = bt_size(bt);
      }
      if (bt_size(bt) < best_s) {
        best = bt;
        best_s = bt_size(bt);
      }
      if (best_s == reqsz) {
        return best;
      }
    }
    if (reqsz > bt_size(bt))
      bt = bt_get_r_ptr(bt);
    else if (reqsz < bt_size(bt))
      bt = bt_get_l_ptr(bt);
  }
  return best;
}
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  word_t *best = NULL;
  size_t bestsize = 0;
  word_t *bt = free_list_start;
  while (bt) {
    if (bt_free(bt) && bt_size(bt) >= reqsz) {
      if (best == NULL) {
        best = bt;
        bestsize = bt_size(bt);
      }
      if (bt_size(bt) < bestsize) {
        best = bt;
        bestsize = bt_size(bt);
      }
      if (bestsize == reqsz) {
        return best;
      }
    }
    bt = bt_get_f_ptr(bt);
  }
  return best;
}
#endif
/*Ustawiamy znaleziony wolny blok na zajęty i w razie potrzeby dzielimy go*/
static void createblock(size_t size, word_t *bt) {
  size_t oldsize = bt_size(bt);
  bt_flags prevfr = bt_get_prevfree(bt);
  if (size == oldsize) {
    free_list_start = delete (bt, free_list_start);
    bt_make(bt, size, (prevfr | USED));
    bt_clr_prevfree(bt_next(bt));
  }
  /*Jeżeli wolny blok był większy niż potrzebny rozmiar rozdzielamy go*/
  else if (oldsize > size) {
    if (oldsize - size >= MINSIZE) {
      free_list_start = delete (bt, free_list_start);
      bt_make(bt, size, (prevfr | USED));
      word_t *next_bt = bt_next(bt);
      bt_make(next_bt, oldsize - size, FREE);
      free_list_start = insert(next_bt, free_list_start);
    } else {
      free_list_start = delete (bt, free_list_start);
      bt_make(bt, oldsize, (prevfr | USED));
      bt_clr_prevfree(bt_next(bt));
    }
  }
}

void *malloc(size_t size) {
  size_t alsize;
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
    bt = mm_extend_heap(alsize);
    if (bt == NULL) {
      return NULL;
    }
    free_list_start = insert(bt, free_list_start);
    createblock(alsize, bt);
    return bt_payload(bt);
  }
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (ptr == NULL) {
    return;
  }
  word_t *bt = bt_fromptr(ptr);
  size_t size = bt_size(bt);
  bt_flags prevfr = bt_get_prevfree(bt);
  bt_make(bt, size, (prevfr | FREE));
  bt_set_prevfree(bt_next(bt));
  bt = coaelesce(bt);
  free_list_start = insert(bt, free_list_start);
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
      bt_flags prevfre = bt_get_prevfree(old_bt);
      bt_make_opt(old_bt, alsize, (prevfre | USED));
      word_t *nextbt = bt_next(old_bt);
      bt_make(nextbt, (old_size - alsize), USED);
      free(bt_payload(nextbt));
      return old_ptr;
    }
    void *newptr = malloc(size);
    if (newptr == NULL) {
      return NULL;
    }
    memcpy(newptr, old_ptr, size);
    free(old_ptr);
    return newptr;
  } else {
    /*Zamiast szukać nowego bloku sprawdzamy najpierw czy możemy się połączyć z
     * następnym blokiem*/
    word_t *next_bt = bt_next(old_bt);
    size_t nextsize = bt_size(next_bt);
    if (bt_free(next_bt) && old_size + nextsize >= alsize) {
      free_list_start = delete (next_bt, free_list_start);
      if ((old_size + nextsize - alsize) >= MINSIZE) {
        bt_flags prevfre = bt_get_prevfree(old_bt);
        bt_make_opt(old_bt, alsize, (prevfre | USED));
        word_t *nextbt = bt_next(old_bt);
        bt_make(nextbt, (old_size + nextsize - alsize), USED);
        free(bt_payload(nextbt));
        return old_ptr;
      }
      bt_flags prevfre = bt_get_prevfree(old_bt);
      bt_make_opt(old_bt, old_size + bt_size(next_bt), (prevfre | USED));
      bt_clr_prevfree(bt_next(old_bt));
      return old_ptr;
    }
    word_t *newptr = malloc(size);
    if (newptr == NULL) {
      return NULL;
    }
    memcpy(newptr, old_ptr, size);
    free(old_ptr);
    return newptr;
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
/*zlicz wolne bloki w drzewie i sprawdza czy wskaźniki są poprawne*/
static int check_tree_n(word_t *bt) {
  int rtval = 1;
  if (bt == NULL) {
    return 0;
  }
  if ((heap_lo_addr > (void *)bt_get_l_ptr(bt) ||
       mem_heap_hi() < (void *)bt_get_l_ptr(bt)) &&
      bt_get_l_ptr(bt) != NULL) {
    printf("Adres poza sterta\n");
    exit(EXIT_FAILURE);
  }
  if ((heap_lo_addr > (void *)bt_get_r_ptr(bt) ||
       mem_heap_hi() < (void *)bt_get_r_ptr(bt)) &&
      bt_get_r_ptr(bt) != NULL) {
    printf("Adres poza sterta \n");
    exit(EXIT_FAILURE);
  }
  rtval += check_tree_n(bt_get_l_ptr(bt));
  rtval += check_tree_n(bt_get_r_ptr(bt));
  return rtval;
}
/* sprawdź czy wszystkie bloki w drzewie oznaczone jako wolne*/
static int check_tree(word_t *bt) {
  int rtval = 1;
  if (bt == NULL) {
    return 1;
  }
  if (bt_used(bt)) {
    rtval = 0;
  }
  if (bt == NULL) {
    return 1;
  }
  rtval = rtval && check_tree(bt_get_l_ptr(bt));
  rtval = rtval && check_tree(bt_get_r_ptr(bt));
  return rtval;
}

void mm_checkheap(int verbose) {
  int fblocks_in_list = 0;
  int fblocks_in_tree = 0;
  int prevfree = 0;
  word_t *bt = heap_start;
  while (!(bt_used(bt) && bt_size(bt) == 0)) {
    if (bt_free(bt)) {
      if (prevfree == 1) {
        printf("dwa przylegle do siebie bloki sa wolne \n");
        exit(EXIT_FAILURE);
      }
      fblocks_in_list += 1;
      prevfree = 1;
    } else {
      prevfree = 0;
    }
    bt = bt_next(bt);
  }
  fblocks_in_tree = check_tree_n(free_list_start);
  if (fblocks_in_list != fblocks_in_tree) {
    printf("Nie wszystkie wolne bloki sa w drzewie splay \n");
    exit(EXIT_FAILURE);
  }
  if (!check_tree(free_list_start)) {
    printf("W drzewie znajduja sie zajete bloki\n");
    exit(EXIT_FAILURE);
  }
}