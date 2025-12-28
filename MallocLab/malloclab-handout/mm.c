/*
 * mm.c - segregated free list allocator (best-fit, realloc optimized)
 *
 * [ design overview ]
 * - structure: segregated free list with explicit pointers (void** seg_list).
 * - placement: best-fit search for better memory utilization.
 * - coalescing: immediate coalescing with boundary tags (lifo policy).
 *
 * [ key features ]
 * 1. segregated list: uses a heap-allocated pointer array instead of a global array
 * to comply with the lab rules.
 * 2. fine-grained indexing: small blocks (16-128 bytes) are indexed in 8-byte steps
 * to minimize internal fragmentation for binary traces.
 * 3. realloc optimization (no-split strategy):
 * - does not split the block to keep the buffer for future growth.
 * - merges with the next free block without splitting.
 * - extends the heap only by the required amount at the heap end.
 *
 * name: seung-hyeon chae
 * student id: 20240832
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // word and header/footer size (bytes)
#define DSIZE 8 // double word size (bytes)
#define CHUNKSIZE (1<<12) // extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc)) // pack a size and allocated bit into a word

// read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// compute address of the predecessor pointer (stored at start of payload)
#define PRED_PTR(bp) ((char *)(bp))

// compute address of the successor pointer (stored after predecessor of pointer)
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

// dereference to get/set the actual predecessor node address
#define GET_PRED(bp) (*(char **)(PRED_PTR(bp)))
#define SET_PRED(bp, ptr) (GET_PRED(bp) = (ptr))

// dereference to get/set the actual successor node address
#define GET_SUCC(bp) (*(char **)(SUCC_PTR(bp)))
#define SET_SUCC(bp, ptr) (GET_SUCC(bp) = (ptr))

// segregated free list
#define LIST_LIMIT 20
void** seg_list; // array of pointers to free lists for different size classes

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t asize);
static void insert_node(void* bp, size_t size);
static void delete_node(void* bp);
static int get_list_index(size_t size);
static void checkblock(void* bp);
static void printblock(void* bp);
int mm_check(void);

int mm_init(void)
{
    int i;
    char* prologue_ptr;

    if ((seg_list = mem_sbrk((LIST_LIMIT * sizeof(void*)) + (4 * WSIZE))) == (void*)-1)
        return -1;

    for (i = 0; i < LIST_LIMIT; i++)
        seg_list[i] = NULL;

    prologue_ptr = (char*)seg_list + (LIST_LIMIT * sizeof(void*));

    PUT(prologue_ptr, 0);
    PUT(prologue_ptr + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(prologue_ptr + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(prologue_ptr + (3 * WSIZE), PACK(0, 1));

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char* bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) asize = 2 * DSIZE;
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

void mm_free(void *ptr)
{
    size_t size;
    if (ptr == NULL)
        return;

    size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
    void* newptr;
    size_t old_size;
    size_t new_size;
    size_t extend_needed;
    size_t combine_size;

    void* next_bp;
    size_t next_alloc;
    size_t next_size;

    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    old_size = GET_SIZE(HDRP(ptr));

    if (size <= DSIZE) new_size = 2 * DSIZE;
    else new_size = DSIZE * ((size + (DSIZE)+(DSIZE - 1)) / DSIZE);

    // policy 1: if new_size is smaller than or equal to old size, return ptr
    // this avoids unecessary copy overhead
    if (new_size <= old_size) {
        return ptr;
    }

    next_bp = NEXT_BLKP(ptr);
    next_alloc = GET_ALLOC(HDRP(next_bp));
    next_size = GET_SIZE(HDRP(next_bp));

    // policy 2: if next block is free and combined_size is enough, coalesce and use it
    combine_size = old_size + next_size;
    if (!next_alloc && (combine_size >= new_size)) {
        delete_node(next_bp);
        PUT(HDRP(ptr), PACK(combine_size, 1));
        PUT(FTRP(ptr), PACK(combine_size, 1));
        return ptr;
    }

    // policy 3: if the block is at the end of heap, extend heap directly
    if (next_size == 0) {
        extend_needed = new_size - old_size;
        if ((long)(mem_sbrk(extend_needed)) == -1)
            return NULL;

        PUT(HDRP(ptr), PACK(new_size, 1));
        PUT(FTRP(ptr), PACK(new_size, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); // restore epilogue header
        return ptr;
    }
    
    // fallback
    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;

    memcpy(newptr, ptr, old_size - DSIZE);
    mm_free(ptr);
    return newptr;
}

static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void* coalesce(void* bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1
    if (prev_alloc && next_alloc) {
        insert_node(bp, size);
        return bp;
    }

    // case 2
    else if (prev_alloc && !next_alloc) {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3
    else if (!prev_alloc && next_alloc) {
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // case 4
    else {
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_node(bp, size);
    return bp;
}

static void place(void* bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    delete_node(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        insert_node(bp, csize - asize);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void* find_fit(size_t asize)
{
    int index = get_list_index(asize);
    void* bp;
    void* best_bp = NULL;
    size_t min_diff = (size_t) - 1;
    int i;

    for (i = index; i < LIST_LIMIT; i++) {
        for (bp = seg_list[i]; bp != NULL; bp = GET_SUCC(bp)) {
            size_t curr_size = GET_SIZE(HDRP(bp));

            if (asize <= curr_size) {
                size_t diff = curr_size - asize;

                if (diff == 0)
                    return bp;

                if (diff < min_diff) {
                    min_diff = diff;
                    best_bp = bp;
                }
            }
        }

        if (best_bp != NULL) {
            return best_bp;
        }
    }
    return best_bp;
}

static int get_list_index(size_t size) {
    if (size <= 16) return 0;
    if (size <= 24) return 1;
    if (size <= 32) return 2;
    if (size <= 40) return 3;
    if (size <= 48) return 4;
    if (size <= 56) return 5;
    if (size <= 64) return 6;
    if (size <= 72) return 7;
    if (size <= 80) return 8;
    if (size <= 88) return 9;
    if (size <= 96) return 10;
    if (size <= 104) return 11;
    if (size <= 112) return 12;
    if (size <= 128) return 13;
    if (size <= 256) return 14;
    if (size <= 512) return 15;
    if (size <= 1024) return 16;
    if (size <= 2048) return 17;
    if (size <= 4096) return 18;
    return 19;
}

static void insert_node(void* bp, size_t size)
{
    int index = get_list_index(size);
    void* root = seg_list[index];

    SET_SUCC(bp, root);
    SET_PRED(bp, NULL);

    if (root != NULL)
        SET_PRED(root, bp);

    seg_list[index] = bp;
}

static void delete_node(void* bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = get_list_index(size);

    if (GET_PRED(bp) != NULL)
        SET_SUCC(GET_PRED(bp), GET_SUCC(bp));
    else
        seg_list[index] = GET_SUCC(bp);

    if (GET_SUCC(bp) != NULL)
        SET_PRED(GET_SUCC(bp), GET_PRED(bp));
}

int mm_check(void)
{
    char* heap_start = (char*)seg_list + (LIST_LIMIT * sizeof(void*)) + (2 * WSIZE);

    char* bp = heap_start;
    int i;
    int free_count_by_heap = 0;
    int free_count_by_list = 0;
    int verbose = 0;

    if (verbose) printf("Heap Start (%p):\n", heap_start);

    if ((GET_SIZE(HDRP(heap_start)) != DSIZE) || !GET_ALLOC(HDRP(heap_start))) {
        printf("Error: Bad prologue header\n");
        exit(1);
    }

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) printblock(bp);
        checkblock(bp);

        if (!GET_ALLOC(HDRP(bp)) && !GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
            printf("Error: Contiguous free blocks not coalesced at %p\n", bp);
            exit(1);
        }

        if (!GET_ALLOC(HDRP(bp))) {
            free_count_by_heap++;
        }
    }

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Error: Bad epilogue header\n");
        exit(1);
    }

    for (i = 0; i < LIST_LIMIT; i++) {
        void* curr = seg_list[i];
        void* prev = NULL;

        while (curr != NULL) {
            if ((char*)curr < (char*)mem_heap_lo() || (char*)curr >(char*)mem_heap_hi()) {
                printf("Error: Free list pointer %p out of bounds in list %d\n", curr, i);
                exit(1);
            }
            if (GET_ALLOC(HDRP(curr))) {
                printf("Error: Allocated block %p in free list %d\n", curr, i);
                exit(1);
            }
            if (prev != NULL && GET_PRED(curr) != prev) {
                printf("Error: Prev pointer inconsistency at %p\n", curr);
                exit(1);
            }
            free_count_by_list++;
            prev = curr;
            curr = GET_SUCC(curr);
        }
    }

    if (free_count_by_heap != free_count_by_list) {
        printf("Error: Free block count mismatch. Heap: %d, List: %d\n",
            free_count_by_heap, free_count_by_list);
        exit(1);
    }

    return 1;
}

static void checkblock(void* bp)
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
        exit(1);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: Header does not match footer at %p\n", bp);
        exit(1);
    }
}

static void printblock(void* bp)
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }
    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
        (int)hsize, (halloc ? 'a' : 'f'),
        (int)fsize, (falloc ? 'a' : 'f'));
}








