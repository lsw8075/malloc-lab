/*
 * mm-seg.c - The segregated-fit, LIFO explcit free list based malloc package with better realloc (93/100).
 *
 * in 2017 Fall System Programming class in SNU
 * by Seungwoo Lee
 * 2017/11/14
 *
 * in this malloc-lab, our memory model is 32-bit
 *
 * overall heap structure:
 *  - heap contains several segregated lists
 *  - the number of seg-list is SEGLIST_COUNT(now 13)
 *  - each seglist contains several free blocks,
 *  - whose size are 2^4..2^5-1, 2^5..2^6-1, ... 2^15..2^16-1, 2^16..inf
 *  - there are SEGLIST_COUNT prolog blocks at the heap start,
 *  - and, also SEGLIST_COUNT epilog blocks at the heap end.
 *  - between prologs and epilogs, there are N>=0 normal blocks.
 *
 * normal block structure
 *  - a normal block is one of allocated block or free block
 *  - every normal block has own header at the start and footer at the end.
 *  - header/footer contains block size and one free bit.
 *  - block size includes header and footer size
 *  - free bit is set in case of free blocks, while not set in the allocated ones.
 *  - a free block contains PRED and SUCC pointer,
 *  - which points to it's predecessor and successor free block respectively.
 *  - minimum block size is 16 byte
 *
 * prolog/epilog block structure
 *  - one prolog block contains a PRED(always NULL), a SUCC, a footer(0).
 *  - one epilog block contains a header(0), a PRED, a SUCC(always NULL).
 *  - header and footer set to 0 as it is neither an allocated block, nor a free one.
 *
 * seg-list structure
 *  - each seg-list is doubly linked list of free blocks
 *  - there are prolog and epilog block on the each end of the seg-list.
 *  - at first, each seg-list contains prolog and epilog block.
 *  - we insert block into the seg-list corresponding to the block size.
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

// for segragated-fit

// in here, lists are 2^4.., 2^5.., ... 2^14...
// the count must be odd number, as 8-byte alignment of block
#define SEGLIST_COUNT 13

// if debug needed, enable this macro
//#define DEBUG

// each seglist has own epilogs and prologs
// all the epilog & prologs are 3-WORD size
// epilog has header, pred, succ of each seglist
// prolog has footer, pred, succ of each seglist

#define EPILOG_SIZE (SEGLIST_COUNT * 3 * WSIZE)
#define PROLOG_SIZE (EPILOG_SIZE)

// debug option

#define BOLDSTART ""//"\033[1m"
#define BOLDEND ""//"\033[0m"

// global pointers
static size_t *ptr_heap, heap_size;

// seglist functions

// determine the which seg-list the free block should go, considering its size.. 
static int seglist_no(size_t v) {
    // performs integer log 2
    // (from 'Bit twiddling hacks' by Sean Anderson)
    size_t r, shift;
    r = (v > 0xFFFF)   << 4; v >>= r;
    shift = (v > 0xFF) << 3; v >>= shift; r |= shift;
    shift = (v > 0xF)  << 2; v >>= shift; r |= shift;
    shift = (v > 0x3)  << 1; v >>= shift; r |= shift;
                                          r |= (v >> 1);
    // seglist starts with 2^4..2^5-1, so 4 is index 0
    int x = (int)r - 4;
    if(x < 0) x = 0;
    if(x >= SEGLIST_COUNT) x = SEGLIST_COUNT - 1;
    return x;
}

// helper macros
#define get_overall_prolog_start() (ptr_heap)
#define get_prolog_block(no) (get_overall_prolog_start() + (no) * 3)
#define get_first_block(no) (*SUCCP(get_prolog_block(no)))
#define get_overall_first_block() (get_overall_prolog_start() + (SEGLIST_COUNT * 3 + 1))
#define get_overall_epilog_start() ((size_t *)((char *)(ptr_heap) + ((heap_size) - EPILOG_SIZE)))
#define get_epilog_block(no) (get_overall_epilog_start() + ((no) * 3 + 1))

// init seg-lists
static void init_seglist() {
#ifdef DEBUG
    printf("initing seglist..\n");
#endif
    int i;
    size_t *p = ptr_heap;
    size_t *pro = get_overall_prolog_start(), *epi = get_overall_epilog_start() + 1;

    // heap starts with prolog list
    // init prolog list
    for(i=0; i<SEGLIST_COUNT; i++) {
        *p = 0; p++;
        *p = (size_t)(epi); p++;
        *p = 0; p++;
        epi += 3;
    }
    // init epilog list
    for(i=0; i<SEGLIST_COUNT; i++) {
        *p = 0; p++;
        *p = (size_t)(pro); p++;
        *p = 0; p++;
        pro += 3;
    }
#ifdef DEBUG
    p = ptr_heap;
    for(i=0; i<SEGLIST_COUNT * 2; i++) {
        printf("initialize %p(%s %d): %d %p %d\n", p+3*i, i/SEGLIST_COUNT ? "epilog" : "prolog",
            i%SEGLIST_COUNT, *(p+3*i), *(p+3*i+1), *(p+3*i+2));
    }

    // test helper macros
    printf("prolog starts at %p, epilog starts at %p\n", get_overall_prolog_start(), get_overall_epilog_start());
#endif
}

// get the last block except epilog blocks.
static size_t *get_overall_last_block() {
    size_t *last_ftrp = get_overall_epilog_start() - 1;
    if(!last_ftrp) return NULL;
    return (size_t *)((char *)last_ftrp - GET_SIZE(last_ftrp) + DSIZE);
}

//debug functions

// print fuction name
static void dump_funcname(char *name) {
    printf("====== function %s%s%s ======\n", BOLDSTART, name, BOLDEND);
}

// dump block
static void dump_block(size_t *bp) {
    printf("%s#block%s %p(%d, %s)\n", BOLDSTART, BOLDEND, bp, GET_SIZE(HDRP(bp)), GET_FREE_BIT(HDRP(bp)) ? "free" : "alloc");
}

// dump header & footer
static void dump_extra(size_t *bp) {
    char p_open, p_close;
    if(GET_FREE_BIT(HDRP(bp))) p_open = '[', p_close = ']';
    else p_open = '(', p_close = ')';

    printf("  HDR: %p%c%d%c FTR: %p%c%d%c\n", HDRP(bp), p_open, GET_SIZE(HDRP(bp)), p_close, FTRP(bp), p_open, GET_SIZE(FTRP(bp)), p_close);
}

// dump link information
static void dump_link(size_t *bp) {
    if(GET_FREE_BIT(HDRP(bp))) {

        int is_prolog = *PREDP(bp) < get_overall_first_block();
        int is_epilog = get_overall_epilog_start() <= *SUCCP(bp);
        int prolog_no = (*PREDP(bp) - get_overall_prolog_start()) / 3;
        int epilog_no = (*SUCCP(bp) - get_overall_epilog_start()) / 3;
        char str_prolog[32] = "", str_epilog[32] = "";
        if(is_prolog) sprintf(str_prolog, "(prolog of %d)", prolog_no);
        if(is_epilog) sprintf(str_epilog, "(epilog of %d)", epilog_no);

        printf("  PRED: %p%s SUCC: %p%s\n", *PREDP(bp), str_prolog, *SUCCP(bp), str_epilog);
    }
}

// function for error handling
void handle_error(size_t *bp, char *msg) {
    printf("<<<<<<%s>>>>>>\n", msg);
    if(bp) {
        dump_block(bp);
        dump_extra(bp);
        if(GET_FREE_BIT(HDRP(bp)))
            dump_link(bp);
    }
    exit(1);
}

// simple memory check function
int mm_check(void) {
    // check all blocks are in free list is really free
    
    size_t *cur_block;

    cur_block = get_overall_first_block(); // first block of block list

    // loop in block list until first epliog block
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
        }
        cur_block = NEXT_BLKP(cur_block);
    }

    // loop in free list until epliog block
    int no;
    for(no=0; no<SEGLIST_COUNT; no++) {
        cur_block = get_first_block(no); // first block of each free list
        while(*HDRP(cur_block)) {
            // check every block in the free list is really free
            if(!GET_FREE_BIT(HDRP(cur_block)))
                handle_error(cur_block, "allocated block in free list");
            cur_block = *SUCCP(cur_block);
        }
    }
    
    return 1;
}

// dump all normal blocks in the heap
static int mm_dump(char *str, void *addr, int s)
{
    printf("===starting mem dump : %s(%p, %d)===\n", str, addr, s);
    // print current memory state
    size_t *cur_block = get_overall_first_block();
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

// list functions

// insert a free block into the seg-list, correspond to its size
static void insert_to_free_list(size_t *bp) {

    int which_list = seglist_no(GET_SIZE(HDRP(bp)));

    // use LIFO strategy at seglist
    size_t *pred_free = get_prolog_block(which_list);
    size_t *succ_free = get_first_block(which_list);

    *PREDP(bp) = pred_free;
    *SUCCP(bp) = succ_free;

    *SUCCP(pred_free) = bp;
    *PREDP(succ_free) = bp;

}

// remove a free block from seg-list
static void remove_from_free_list(size_t *bp) {

    size_t *pred_free = *PREDP(bp);
    size_t *succ_free = *SUCCP(bp);

    *SUCCP(pred_free) = succ_free;
    *PREDP(succ_free) = pred_free;
}   

// function for heap initialization
int mm_init(void) {

#ifdef DEBUG
    dump_funcname("mm_init");
#endif

    heap_size = PROLOG_SIZE + EPILOG_SIZE;
    ptr_heap = mem_sbrk(heap_size);

    // initialize prolog & epilogs of each seglist

    init_seglist();

    return 0;
}

// get adjusted block size including header and footer
static size_t get_adjusted_size(size_t size) {
    // align block size to 8 byte
    return ALIGN(size) + DSIZE;
}


// find first-fit of size, starting at seglist of start_no, working recursively.

static void *find_fit(size_t size, int start_no) {

    if(start_no >= SEGLIST_COUNT)
        return NULL; // no block found. expansion needed;
#ifdef DEBUG
    printf("finding fit(%d) in list %d\n", size, start_no);
#endif
    // start at first block of free list
    size_t *cur_block = get_first_block(start_no);

    // loop until epliog block
    while(*HDRP(cur_block)) {
        if(GET_FREE_BIT(HDRP(cur_block)) && GET_SIZE(HDRP(cur_block)) >= size)
            return cur_block;
        cur_block = *SUCCP(cur_block);
    }

    // if block is not found, search larger seglist
    return find_fit(size, start_no + 1);
}

// expand heap & shift the epilogs
static void expand_heap(size_t size) {

    size_t *old_epilog_start = get_overall_epilog_start();
    size_t *new_epilog_start = (size_t *)((char *)mem_sbrk(size) + size - EPILOG_SIZE);

    if(!new_epilog_start) {
        handle_error(NULL, "Out of memory");
    }

    heap_size += size;
    // first, move epilog
    memmove(new_epilog_start, old_epilog_start, EPILOG_SIZE);

    // update SUCC of epilog pred
    int i;
    size_t *each_epilog = new_epilog_start + 1;
    for(i=0; i<SEGLIST_COUNT; i++) {
        *SUCCP(*PREDP(each_epilog)) = each_epilog;
        each_epilog += 3;
    }
#ifdef DEBUG
    printf("expand heap in %d bytes.. new epilog blocks\n", size);
#endif
}

// place the block
static void place(size_t *addr, size_t size, int is_free) {
    // place block header and footer
    PUT(HDRP(addr), PACK(size, is_free));
    PUT(FTRP(addr), PACK(size, is_free));
}

// our malloc function: find fit, then alloc or split-alloc or expand
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

    // find fit, starting smallest possible seglist
    if((bp = find_fit(asize, seglist_no(asize)))) {
        // if fit is found
        remove_from_free_list(bp);
        // check whether splitting is possible  
        size_t block_size = GET_SIZE(HDRP(bp));
        if(block_size - asize >= MIN_BLOCK_SIZE) {

            // case: split
            place(bp, asize, 0);
            size_t * free_area = NEXT_BLKP(bp);
            place(free_area, block_size - asize, 1);
            insert_to_free_list(free_area);

#ifdef DEBUG
            printf("found fit at %p: %d ==split==> %d + %d\n", bp, block_size, asize, block_size - asize);
            dump_extra(bp);
            dump_extra(free_area);
#endif

        } else {
            // non-split
            place(bp, block_size, 0);
#ifdef DEBUG
            printf("found fit at %p: %d of %d\n", bp, block_size, asize);
            dump_extra(bp);
#endif
        }
        
    } else {
        // expand the heap if fails

#ifdef DEBUG
        printf("try expansion...\n");
#endif 
        // if last block is free area
        if(GET_FREE_BIT(get_overall_epilog_start() - 1)) {
            bp = get_overall_last_block();
            remove_from_free_list(bp);
            size_t last_block_size = GET_SIZE(HDRP(bp));
            expand_heap(asize - last_block_size);
        } else {
            // set bp at the position of old epilog
            bp = get_overall_epilog_start() + 1;
            expand_heap(asize);
        }

        // set the new block at bp
        place(bp, asize, 0);
    }

#ifdef DEBUG
    mm_dump("malloc", bp, asize);
#endif

    return bp;

}

// our free function: with coalescing
void mm_free(void *ptr)
{
    size_t *bp = (size_t *)ptr;

    size_t size = GET_SIZE(HDRP(bp));

    place(ptr, size, 1);

    size_t prev_free = GET_FREE_BIT(GET_PREV_FTRP(bp));
    size_t next_free = GET_FREE_BIT(GET_NEXT_HDRP(bp));

    size_t *prev_block = PREV_BLKP(bp);
    size_t *next_block = NEXT_BLKP(bp);

#ifdef DEBUG
    dump_funcname("mm_free");
    printf("freeing block at %p(%d) ", bp, size);
    if(prev_free | next_free) printf("coalesce:");
    if(prev_free) printf(" %p", prev_block);
    if(next_free) printf(", %p",next_block);
    printf("\n");
    dump_extra(bp);
#endif

    // coalesce blocks
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

// our realloc function: try utilizing next block & autonomous heap expansion
void *mm_realloc(void *ptr, size_t size)
{
#ifdef DEBUG
    dump_funcname("mm_realloc");
#endif

    // if ptr == NULL, malloc
    if(!ptr) return mm_malloc(size);
    
    // if size == 0, free
    if(!size) {
        mm_free(ptr);
        return NULL;
    }

    size_t asize = get_adjusted_size(size);
    size_t cur_size = GET_SIZE(HDRP(ptr));

    void * oldptr = ptr;

#ifdef DEBUG
    printf("realloc %p(%d -> %d)\n", ptr, cur_size, asize);
#endif

    // first check whether surrounding free blocks exist

    // no utilizing with prev block.. it hinders overall utilization rate
    size_t prev_free = 0;//GET_FREE_BIT(GET_PREV_FTRP(ptr));
    size_t next_free = GET_FREE_BIT(GET_NEXT_HDRP(ptr));

    size_t prev_size = GET_SIZE(GET_PREV_FTRP(ptr));
    size_t next_size = GET_SIZE(GET_NEXT_HDRP(ptr));

    size_t *prev_block = PREV_BLKP(ptr);
    size_t *next_block = NEXT_BLKP(ptr);
    size_t *new_block;
    size_t total_size, new_block_size;

    // check is expandable block..
    size_t is_last = get_overall_last_block() == ptr;
    
    // data size to copy/move
    size_t data_size = (asize < cur_size ? asize : cur_size) - DSIZE;
    if(prev_free && next_free && (prev_size + cur_size + next_size >= asize || is_last)) {
        // utilize both side
        total_size = prev_size + cur_size + next_size;
        remove_from_free_list(prev_block);
        remove_from_free_list(next_block);
        ptr = memmove(prev_block, ptr, data_size);        
    } else if(!prev_free && next_free && (cur_size + next_size >= asize || is_last)) {
        // utilize next side 
        total_size = cur_size + next_size;
        remove_from_free_list(next_block);
    } else if(prev_free && !next_free && (prev_size + cur_size >= asize || is_last)) {
        // utilize prev side
        total_size = prev_size + cur_size;
        remove_from_free_list(prev_block);
        ptr = memmove(prev_block, ptr, data_size);        
    } else if(!prev_free && !next_free && (cur_size >= asize || is_last)) {
        total_size = cur_size;
    } else {
        // in this case, we will use simply malloc & free.. 
        size_t *temp = mm_malloc(asize);
        memcpy(temp, ptr, data_size);
        mm_free(ptr);

        return temp;
    }

    if(total_size < asize) {
        if(!is_last) {
            handle_error(ptr, "Illegal condition check in realloc");
            exit(1);
        }
        // expand the heap
        expand_heap(asize - total_size);

        place(ptr, asize, 0);
        new_block = NULL;
    } else {

        new_block_size = total_size - asize;

        // determine to split
        if(new_block_size >= MIN_BLOCK_SIZE) {
            // split
            // set header & footer
            place(ptr, asize, 0);

            // set new block
            new_block = FTRP(ptr) + 2;
            place(new_block, new_block_size, 1);
            insert_to_free_list(new_block);
        } else {
            // non-split
            place(ptr, total_size, 0);
            new_block = NULL;
        }
    }

#ifdef DEBUG
    printf("reallocate block %p(%d) ", oldptr, cur_size);
    printf("coalesce:");
    if(prev_free) printf(" %p(%d)", prev_block, prev_size);
    if(next_free) printf(", %p(%d)", next_block, next_size);
    printf("\nto block %p(%d)\n", ptr, asize);
    if(new_block) {
        printf("new ");
        dump_block(new_block);
        dump_extra(new_block);
        dump_link(new_block);
    }
    mm_dump("realloc", oldptr, asize);
#endif

    return ptr;
}
