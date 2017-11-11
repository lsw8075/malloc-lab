/*
 * mm-explicit.c - The first-fit, explcit free list based malloc package.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE   4   /* word size (bytes) */
#define DSIZE   8   /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD  8   /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)     (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)     (size_t *)((char *)(bp) - WSIZE)
#define FTRP(bp)     (size_t *)((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  (size_t *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  (size_t *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// use alloc bit as free bit
// if alloc bit is 0, it indicates allocated block
// if alloc bit is 1, it indicates free block

#define GET_FREE_BIT(p) GET_ALLOC(p)
#define GET_PREV_FTRP(bp) (size_t *)((char *)(bp) - DSIZE)
#define GET_NEXT_HDRP(bp) (size_t *)((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)

// if header or footer is 0, it indicates the prolog or epilog

#define MIN_BLOCK_SIZE 16

// below macros for the explicit free list

// only for free blocks

#define PREDP(fbp) ((size_t **)(fbp))
#define SUCCP(fbp) ((size_t **)((char *)(fbp) + WSIZE))

// #define DEBUG
#define BOLDSTART "\033[1m"
#define BOLDEND "\033[0m"
// pointers
size_t *first_block, *prolog_block, *epilog_block;


//debug functions

static void dump_funcname(char *name) {
    printf("====== function %s%s%s ======\n", BOLDSTART, name, BOLDEND);
}

static void dump_block(void *bp) {
    printf("%s#block%s %p(%d, %s)\n", BOLDSTART, BOLDEND, bp, GET_SIZE(HDRP(bp)), GET_FREE_BIT(HDRP(bp)) ? "free" : "alloc");
}

static void dump_extra(void *bp) {
    char p_open, p_close;
    if(GET_FREE_BIT(HDRP(bp))) p_open = '[', p_close = ']';
    else p_open = '(', p_close = ')';

    printf("  HDR: %p%c%d%c FTR: %p%c%d%c\n", HDRP(bp), p_open, GET_SIZE(HDRP(bp)), p_close, FTRP(bp), p_open, GET_SIZE(FTRP(bp)), p_close);
}

static void dump_link(void *bp) {
    if(GET_FREE_BIT(HDRP(bp))) {
        printf("  PRED: %p%s SUCC: %p%s\n", *PREDP(bp), *PREDP(bp) == prolog_block ? "(prolog)" : "", *SUCCP(bp), *SUCCP(bp) == epilog_block ? "(epilog)" : "");
    }
}

int mm_dump(char *str, void *addr, int s)
{
    printf("===starting mem dump : %s(%p, %d)===\n", str, addr, s);
    // print current memory state
    size_t *cur_block = prolog_block + 4;
    while(*HDRP(cur_block)) {
        dump_block(cur_block);
        dump_extra(cur_block);
        dump_link(cur_block);
        cur_block = NEXT_BLKP(cur_block);
    }
    printf("===finishing mem dump===\n");
    // do some check
    return mm_check();
}

void insert_to_free_list(size_t *bp) {

    // use LIFO strategy
    size_t *pred_free = prolog_block;
    size_t *succ_free = first_block;
    first_block = bp;

    *PREDP(bp) = pred_free;
    *SUCCP(bp) = succ_free;

    *SUCCP(pred_free) = bp;
    *PREDP(succ_free) = bp;

}

void remove_from_free_list(size_t *bp) {

    size_t *pred_free = *PREDP(bp);
    size_t *succ_free = *SUCCP(bp);

    if(first_block == bp)
        first_block = succ_free;

    *SUCCP(pred_free) = succ_free;
    *PREDP(succ_free) = pred_free;
}   

int mm_init(void) {

#ifdef DEBUG
    dump_funcname("mm_init");
#endif

    size_t * ptr_heap = mem_sbrk(WSIZE * 6);
    prolog_block = ptr_heap;
    first_block = epilog_block = ptr_heap + 4;
    // initialize prolog & epilog
    // their free bit is not set, but do have PRED/SUCC ptr
    *(ptr_heap++) = 0;                      // prolog PRED
    *(ptr_heap++) = (size_t) epilog_block;  // prolog SUCC
    *(ptr_heap++) = 0;                      // prolog footer
    *(ptr_heap++) = 0;                      // epilog header
    *(ptr_heap++) = (size_t) prolog_block;  // epilog PRED
    *(ptr_heap++) = 0;                      // epilog SUCC

#ifdef DEBUG
    printf("prolog: %p, epilog: %p\n", prolog_block, epilog_block);
#endif
    return 0;
}

static size_t get_adjusted_size(size_t size) {
    // align block size to 8 byte
    return ALIGN(size) + DSIZE;
}

static void *find_fit(size_t size) {

    // start at first block of free list
    size_t *cur_block = first_block;

    // loop until epliog block
    while(*HDRP(cur_block)) {
        if(GET_FREE_BIT(HDRP(cur_block)) && GET_SIZE(HDRP(cur_block)) >= size)
            return cur_block;
        cur_block = *SUCCP(cur_block);
    }
    
    return NULL;
}

// caution at malloc and free:
// the update order of header and footer matter
// as we get the size at the header

void *mm_malloc(size_t size) {

#ifdef DEBUG
    dump_funcname("mm_malloc");
#endif

    if(size == 0)
        return NULL;

    size_t asize = get_adjusted_size(size);
    size_t *bp;

#ifdef DEBUG
    printf("size: %d -> %d\n", size, asize);
#endif

    // find fit
    if((bp = find_fit(asize))) {
        // if fit is found
        remove_from_free_list(bp);
        // check whether splitting is possible  
        size_t block_size = GET_SIZE(HDRP(bp));
        if(block_size - asize >= MIN_BLOCK_SIZE) {

            // case: split
            // first, place the block
            PUT(HDRP(bp), PACK(asize, 0));
            PUT(FTRP(bp), PACK(asize, 0));

            // and place free area
            size_t * free_area = NEXT_BLKP(bp);
            size_t free_size = block_size - asize;
            PUT(HDRP(free_area), PACK(free_size, 1));
            PUT(FTRP(free_area), PACK(free_size, 1));

            insert_to_free_list(free_area);

#ifdef DEBUG
            printf("found fit at %p: %d ==split==> %d + %d\n", bp, block_size, asize, free_size);
            dump_extra(bp);
            dump_extra(free_area);
#endif

        } else {
            // non-split
            
            // place the block to original block size
            PUT(HDRP(bp), PACK(block_size, 0));
            PUT(FTRP(bp), PACK(block_size, 0));
#ifdef DEBUG
            printf("found fit at %p: %d of %d\n", bp, block_size, asize);
            dump_extra(bp);
#endif
        }
        
    } else {
        // extend the heap if fails
#ifdef DEBUG
        printf("extending heap..\n");
#endif

        // if last block is free area
        if(GET_FREE_BIT(GET_PREV_FTRP(epilog_block))) {
            bp = PREV_BLKP(epilog_block);
            remove_from_free_list(bp);
            size_t last_block_size = GET_SIZE(HDRP(bp));
            // expand the difference
            mem_sbrk(asize - last_block_size);
        } else {
            bp = (size_t *) mem_sbrk(asize);
            bp -= 2;
            if(!bp) return NULL;
        }

        // save the epilog pred info
        size_t *epilog_pred = *PREDP(epilog_block);

        // now bp points to preparatory new block..
        // set the new block at bp
        PUT(HDRP(bp), PACK(asize, 0));
        
        size_t * ftr = FTRP(bp);
        PUT(ftr, PACK(asize, 0));
      
        // if epilog was first free block, shift it's location
        if(first_block == epilog_block)
            first_block = ftr + 2;

        epilog_block = ftr + 2; 
        // set the new epilog block
        PUT(epilog_block - 1, 0);
        PUT(epilog_block, (size_t)epilog_pred);
        PUT(epilog_block + 1, 0);

        // update the list bottom
        *SUCCP(epilog_pred) = epilog_block;
        
        
#ifdef DEBUG
        printf("extend heap at %p: %d\n", bp, asize);
        dump_extra(bp);
        printf("new epilog at %p\n", epilog_block);
#endif
    } 

#ifdef DEBUG
    mm_dump("malloc", bp, asize);
#endif

    return bp;

}

void mm_free(void *ptr)
{
    size_t *bp = (size_t *)ptr;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));

    // coalesce blocks
    size_t prev_free = GET_FREE_BIT(GET_PREV_FTRP(bp));
    size_t next_free = GET_FREE_BIT(GET_NEXT_HDRP(bp));

    size_t *prev_block = PREV_BLKP(bp);
    size_t *next_block = NEXT_BLKP(bp);

#ifdef DEBUG
    dump_funcname("mm_free");
    printf("freeing block at %p(%d) ", bp, size);
    printf("coalesce:");
    if(prev_free) printf(" %p", prev_block);
    if(next_free) printf(", %p",next_block);
    printf("\n");
    dump_extra(bp);
#endif

    if(prev_free && next_free) {
        remove_from_free_list(prev_block);
        remove_from_free_list(next_block);
        size += GET_SIZE(GET_PREV_FTRP(bp)) + GET_SIZE(GET_NEXT_HDRP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
    } else if(!prev_free && next_free) { 
        remove_from_free_list(next_block);
        size += GET_SIZE(GET_NEXT_HDRP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(HDRP(bp), PACK(size, 1));
    } else if(prev_free && !next_free) {
        remove_from_free_list(prev_block);
        size += GET_SIZE(GET_PREV_FTRP(bp));
        PUT(FTRP(bp), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
    }

    insert_to_free_list(bp);

#ifdef DEBUG
    printf("new ");
    dump_block(bp);
    dump_extra(bp);
    mm_dump("free", ptr, 0);
#endif
}

size_t mm_size(void *ptr) {
    return GET_SIZE(HDRP(ptr)) - DSIZE;
}

void *mm_realloc(void *ptr, size_t size)
{
#ifdef DEBUG
    dump_funcname("mm_realloc");
#endif

  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL)
    return NULL;
  copySize = mm_size(ptr);
  if (size < copySize)
    copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}

void handle_error(size_t *bp, char *msg) {
    printf("<<<<<<%s>>>>>>\n", msg);
    dump_block(bp);
    dump_extra(bp);
    if(GET_FREE_BIT(HDRP(bp)))
        dump_link(bp);
    exit(1);
}
int mm_check(void) {
    // check all blocks are in free list is really free
    
    size_t *cur_block;

    cur_block = prolog_block + 4; // first block of block list

    // loop in block list until epliog block
    while(*HDRP(cur_block)) {
        // check if current block header and footer are same
        if(*HDRP(cur_block) != *FTRP(cur_block))
            handle_error(cur_block, "header and footer are mismatch");
        if(GET_FREE_BIT(HDRP(cur_block))) {
            // check coalescing
            if(GET_FREE_BIT(GET_PREV_FTRP(cur_block)))
                handle_error(cur_block, "prev coalescing error");
            if(GET_FREE_BIT(GET_NEXT_HDRP(cur_block)))
                handle_error(cur_block, "next coalescing error");
            
            // TODO : check missing free block
        }
        cur_block = NEXT_BLKP(cur_block);
    }

    // loop in free list until epliog block
    cur_block = first_block; // first block of free list
    while(*HDRP(cur_block)) {
        // check every block in the free list is really free
        if(!GET_FREE_BIT(HDRP(cur_block)))
            handle_error(cur_block, "allocated block in free list");
        cur_block = *SUCCP(cur_block);
    }
    
    return 1;
}
