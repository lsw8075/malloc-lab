/*
 * mm-firstfit.c - The first-fit, implcit free list based malloc package.
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


// pointer to first block
size_t * first_block;
size_t * epilog_block;
#ifdef DEBUG

//debug functions

static void dump_funcname(char *name) {
    printf("====== function \033[1m%s\033[0m ======\n", name);
}

static void dump_block(void *bp) {
    printf("block %p(%d, %s)\n", bp, GET_SIZE(HDRP(bp)), GET_FREE_BIT(HDRP(bp)) ? "free" : "alloc");
}

static void dump_extra(void *bp) {
    char p_open, p_close;
    if(GET_FREE_BIT(bp)) p_open = '[', p_close = ']';
    else p_open = '(', p_close = ')';

    printf("block %p: HDR: %p%c%d%c FTR: %p%c%d%c\n", bp, HDRP(bp), p_open, GET_SIZE(HDRP(bp)), p_close, FTRP(bp), p_open, GET_SIZE(FTRP(bp)), p_close);
}

#endif

int mm_init(void) {

#ifdef DEBUG
    dump_funcname("mm_init");
#endif

    size_t * initial_heap = (char *)mem_sbrk(WSIZE * 2);
    
    //initialize prolog footer and epilog header
    first_block = initial_heap;
    *(first_block++) = 0;
    *(first_block++) = 0;
    
    epilog_block = first_block;
#ifdef DEBUG
    printf("%p %p %x %x\n", initial_heap, first_block, initial_heap[0], initial_heap[1]);
#endif
    return 0;
}

static size_t get_adjusted_size(size_t size) {
    // align block size to 8 byte
    return ALIGN(size) + DSIZE;
}

static void *find_fit(size_t size) {

    // start at dummy block
    size_t *cur_block = first_block;

    // loop until epliog block
    while(*HDRP(cur_block)) {
        if(GET_FREE_BIT(HDRP(cur_block)) && GET_SIZE(HDRP(cur_block)) >= size)
            return cur_block;
        cur_block = NEXT_BLKP(cur_block);
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
    size_t * bp;

#ifdef DEBUG
    printf("size: %d -> %d\n", size, asize);
#endif

    // find fit
    if((bp = find_fit(asize))) {
        // if fit is found
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

        // if last block is free area
        if(GET_FREE_BIT(GET_PREV_FTRP(epilog_block))) {
            bp = PREV_BLKP(epilog_block);
            size_t last_block_size = GET_SIZE(HDRP(bp));

            // expand the difference
            mem_sbrk(asize - last_block_size);
        } else {
            bp = (size_t *) mem_sbrk(asize);
            if(!bp) return NULL;
        }

        // now bp points to preparatory new block..
        // set the new block at bp
        PUT(HDRP(bp), PACK(asize, 0));
        PUT(FTRP(bp), PACK(asize, 0));
        
        // set the new epilog block header
        PUT(FTRP(bp) + 1, 0);

#ifdef DEBUG
        printf("extend heap at %p: %d\n", bp, asize);
        dump_extra(bp);
        printf("new epilog at %p\n", FTRP(bp) + WSIZE);
        mm_dump("malloc", bp, asize);
#endif
    } 

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

#ifdef DEBUG
    dump_funcname("mm_free");
    printf("freeing block at %p: %d ", bp, size);
    printf("coalesce: %c, %c\n", prev_free ? 'T' : 'F', next_free ? 'T' : 'F');
    dump_extra(bp);
#endif

    if(prev_free && next_free) {
        size += GET_SIZE(GET_PREV_FTRP(bp)) + GET_SIZE(GET_NEXT_HDRP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
    } else if(!prev_free && next_free) { 
        size += GET_SIZE(GET_NEXT_HDRP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(HDRP(bp), PACK(size, 1));
    } else if(prev_free && !next_free) {
        size += GET_SIZE(GET_PREV_FTRP(bp));
        PUT(FTRP(bp), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
    }

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

int mm_check(void) {
    return 1;
}

#ifdef DEBUG
int mm_dump(char *str, int addr, int s)
{
    printf("===starting mem dump : %s(%p, %d)===\n", str, addr, s);
    // print current memory state
    size_t *cur_block = first_block;
    while(*HDRP(cur_block)) {
        // check if current block header and footer are same
        if(*HDRP(cur_block) != *FTRP(cur_block)) {
            printf("error: header and footer are different at %p(%d, %d)\n", cur_block, *HDRP(cur_block), *FTRP(cur_block));
            return 0;
        }
        dump_block(cur_block);
        dump_extra(cur_block);
        cur_block = NEXT_BLKP(cur_block);
        printf("extra dump: %p %p\n", cur_block, HDRP(cur_block));
    }
    printf("===finishing mem dump===\n");
  return 1;
}
#endif
