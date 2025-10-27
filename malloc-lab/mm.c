/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// build시 적용 방법
#if defined(FIT_FIRST)
  #define USE_FIRST 1
#elif defined(FIT_NEXT)
  #define USE_NEXT 1
#elif defined(FIT_EXPLI)
  #define USE_EXPLI 1
#elif defined(FIT_EXPLI_BEST)
  #define USE_EXPLI_BEST 1
#else
  #define USE_FIRST 1  // default
#endif

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8
/*
malloc은 어떤 타입에도 쓸 수 있어야 함 → 16B 정렬 필요(64bit 환경)
*/
#define ALIGNMENT 8  // 64비트 안전한 기본값

/*
    •   alloc은 0 또는 1
    •   1: 이 블록은 할당됨 (allocated)
    •   0: 가용 상태 (free)
    */
#define ALLOC 1
#define FREE 0

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
WSIZE, DSIZE, CHUNKSIZE => 기본 size 상수 정의( 초기 가용 블록과 힙 확장을 위한 기본 크기 CHUNKSIZE)
PACK 크기와 할당 비트를 통합하여 header와 footer에 저장할 수 있는 값을 리턴
*/
#define WSIZE 4                                                             /* Word and header/footer size (bytes) */
#define DSIZE 8                                                             /* Double word size (bytes)*/
#define CHUNKSIZE (1 << 12)                                                 /* Extend heap by this amount (bytes) == 4096 */
#define MAX(x, y) ( (x) > (y) ? (x) : (y))                                  /* 최대 값 확인 Util*/
#define PACK(size, alloc) ((size) | (alloc))                                /* Pack a size and allocated bit into a word */
#define GET(p) (*(unsigned int *)(p))                                       /* Read a word at address p / 4 Byte 형태로 메모리에서 데이터를 읽겠다. */
#define PUT(p, val) (*(unsigned int *)(p) = (val))                          /* write a word at address p */

#define GET_SIZE(p) (GET(p) & ~0x7)                                         /* Read the size from address p */
/* 할당 여부를 받는 매크로 함수: 0 or 1만 결과 값으로 나오게 되어있음 */
#define GET_ALLOC(p) (GET(p) & 0x1)                                         /* Read Allocated fields from address p */
/* 
                              BP
|----Footer----|----Header----|----Block----|----Footer----|
|----4 Byte----|----4 Byte----|----Block----|----4 Byte----| 
*/
#define HDRP(bp) ((char *)(bp) - WSIZE)                                     /* Given block ptr bp, compute address of its header */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)                /* Given block ptr bp, compute address of its footer */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))     /* Given block ptr bp, compute address of next blocks */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))     /* Given block ptr bp, compute address of previous blocks */

// explicit
// free block payload 앞부분을 포인터 필드로 사용
#define PRED_PTR(bp) ((void **)(bp))
#define SUCC_PTR(bp) ((void **)(bp) + 1)
#define PRED(bp) (*((void **)(bp)))
#define  SUCC(bp) (*((void **)(bp) + 1))

typedef unsigned long dword_t;
typedef char* byte_p;

static void *g_next_p;
static char *heap_listp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

// explicit
static void *free_list_head = NULL;
static void insert_free(void *bp);
static void remove_free(void *bp);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 초기화된 heap 생성
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }

    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    free_list_head = NULL;
    #endif
    PUT(heap_listp, 0);                                /* Alignment padding */
    /* Prologue block은 Header + Footer (8 Bytes)로 구성된다. */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, ALLOC)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, ALLOC)); /* Prologue footer */
    /* Epilogue block은 Header(4 Bytes)로 구성된다. + Prologue, Epilogue는 초기화 과정에서 생성되며 절대 반환하지 않음*/
    PUT(heap_listp + (3 * WSIZE), PACK(0, ALLOC));     /* Epilogue header */
    heap_listp += (2 * WSIZE);
    g_next_p = heap_listp;
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes 
    "초기 가용 블록" 생성 + 실패 시 초기화 중단 용도.
    */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 힙을 짝수로 늘리려고 사이즈를 반올린다.히히
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // brk를 통해 heap 영역의 확장 및 결과 확인
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    if (size <= DSIZE)
        asize = 4 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    #else
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    #endif

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

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    // 전부 0으로 처리
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}
/*
현재 bp가 가리키는 free 블록 주변의 가용 블록과 병합
*/
static void *coalesce(void *bp){
    // 이전 블록의 footer에서 할당 비트를 읽음 (현재 블록의 header 이전 워드)
    size_t prev_alloc = GET_ALLOC(HDRP(bp) - WSIZE);  // 안전한 방법
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    /* Case 1
    이전 블록, 다음 블록 모두 할당되어 있음
    */
    if (prev_alloc && next_alloc) {
        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        insert_free(bp);
        #endif          
        return bp;
    }
    /* Case 2 
    이전 블록은 할당, 다음 블록은 free
    */
    else if(prev_alloc && !next_alloc) {
        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        remove_free(NEXT_BLKP(bp));
        #endif
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, FREE));
        PUT(FTRP(bp), PACK(size, FREE));
    }
    /* Case 3 
    이전 블록은 free, 다음 블록은 할당
    */
    else if(!prev_alloc && next_alloc) {
        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        remove_free(PREV_BLKP(bp));
        #endif
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
    }
    /* Case 3 
    이전 블록 free, 다음 블록 free
    */
    else {
        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        remove_free(PREV_BLKP(bp));
        remove_free(NEXT_BLKP(bp));
        #endif
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
    }
    
    // 탐색이 끝나는 pointer를 변수로 저장
    g_next_p = bp;
    // explicit
    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    insert_free(bp);
    #endif
    return bp;
}

static void *find_fit(size_t asize)
{
    // implicit first_fit, next_fit
    void *bp;
    void *best_bp;      // 가장 좋은 블록 저장
    size_t best_size = (size_t)-1;   // 가장 좋은 블록의 크기
    #if defined(USE_FIRST)
    for ( bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }

    #elif defined(USE_NEXT)
    // g_next_p를 기준으로 뒤쪽(힙 끝 방향)을 먼저 보고, 거기 없으면 앞쪽(힙의 시작 방향)을 다시 본다.
    // Next-fit: 이전 검색이 끝난 위치(g_next_p)부터 시작
    for (bp = g_next_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            g_next_p = bp;
            return bp;
        }
    }

    // 끝까지 못 찾으면 힙의 처음부터 g_next_p 전까지 검색
    for (bp = heap_listp; bp < g_next_p; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) 
        {
            g_next_p = bp;
            return bp;
        }
    }
    #elif defined(USE_EXPLI)
    for ( bp = free_list_head; bp != NULL; bp = SUCC(bp)){
        if ((asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    #elif defined(USE_EXPLI_BEST)
    best_bp = NULL;
    for (bp = free_list_head; bp != NULL; bp = SUCC(bp)) {
        // 여기서 무엇을 비교해야 할까?
        // 언제 best_bp를 업데이트할까?
        size_t curr_size = GET_SIZE(HDRP(bp));

        // 1. asize보다 작으면 스킵
        if (curr_size < asize) {
              continue;
        }

        // 2. asize 이상이면서 이전 best보다 작은 경우
        if (curr_size < best_size) {
            best_bp = bp;
            best_size = curr_size;

            // 3. 완벽하게 맞으면 조기 종료
            if (curr_size == asize) {
                break;
            }
        }
      }
    return best_bp;
    #endif
    return NULL;
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 알아냄
    void *next_bp;

    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    remove_free(bp);
    #endif

    // 남은 공간이 충분히 클 경우, 즉 요청한 크기(asize)와 현재 크기(csize)의 차이가
    // 두 배의 더블 사이즈(DSIZE)보다 크거나 같으면 블록을 나눔

    // explicit에서는 Free Block 레이아웃에 PRED와 SUCC가 추가가 되어 최소 24bit의 공간을 필요로 함
    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    if ((csize - asize) >= (4 * DSIZE))
    #else
    if ((csize - asize) >= (2 * DSIZE))
    #endif
    {
        PUT(HDRP(bp), PACK(asize, 1));         // 사용할 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(asize, 1));         // 사용할 블록의 푸터에도 똑같이 저장
        next_bp = NEXT_BLKP(bp);
        // bp = NEXT_BLKP(bp);                    // 나머지 블록으로 포인터 이동
        PUT(HDRP(next_bp), PACK(csize - asize, 0)); // 나머지 블록의 헤더에 크기와 빈 상태 저장
        PUT(FTRP(next_bp), PACK(csize - asize, 0)); // 나머지 블록의 푸터에도 똑같이 저장

        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        insert_free(next_bp);  // 남은 블록을 free list에 추가
        #endif
    }
    else // 남은 공간이 충분히 크지 않으면 현재 블록 전체 사용
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 현재 블록의 헤더에 크기와 할당된 상태 저장
        PUT(FTRP(bp), PACK(csize, 1)); // 현재 블록의 푸터에도 똑같이 저장
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    // 최적화 1: 현재 블록 크기 확인
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t asize;

    // 필요한 크기 계산
    #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
    if (size <= DSIZE)
        asize = 4 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    #else
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    #endif

    // 최적화 2: 현재 블록이 충분하면 그대로 반환
    if (old_size >= asize) {
        return ptr;
    }

    // 최적화 3: 다음 블록이 free이면 병합 시도
    void *next_bp = NEXT_BLKP(ptr);
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t next_size = GET_SIZE(HDRP(next_bp));

    if (!next_alloc && (old_size + next_size) >= asize) {
        #if defined(USE_EXPLI) || defined(USE_EXPLI_BEST)
        remove_free(next_bp);
        #endif
        PUT(HDRP(ptr), PACK(old_size + next_size, 1));
        PUT(FTRP(ptr), PACK(old_size + next_size, 1));
        return ptr;
    }
    #endif

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

// explicit
static void insert_free(void *bp) 
{
    /* LIFO로 head에 붙이기 */  
    if (free_list_head == NULL) {
        SUCC(bp) = NULL;
        PRED(bp) = NULL;
        free_list_head = bp;
    } else {
        SUCC(bp) = free_list_head;
        PRED(bp) = NULL;
        PRED(free_list_head) = bp;
        free_list_head = bp;
    }
}
static void remove_free(void *bp) 
{
    void *prev = PRED(bp);
    void *next = SUCC(bp);

    if(prev == NULL && next == NULL){
        // 리스트에 bp만 있는 경우
        free_list_head = NULL;
    }
    else if(prev == NULL){
        // bp가 head일 때
        free_list_head = next;
        if (next) PRED(next) = NULL;
    }else if(next == NULL){
        // bp가 tail일 때
        SUCC(prev) = NULL;
    }else{
        // bp가 중간 노드일 때
        SUCC(prev) = next;
        PRED(next) = prev;
    }
     /* prev/next 포인터 정리 */ 
}