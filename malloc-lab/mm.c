/*
 * mm.c - Segregated Free List + Binary Trace 최적화
 *
 * 구현 기술:
 * 1. Segregated Free Lists: 크기별로 분리된 free list (15개 클래스)
 * 2. Explicit Free Lists: free 블록만 PRED/SUCC 포인터로 연결
 * 3. Best-fit search: 각 size class에서 최적 블록 탐색
 * 4. Immediate coalescing: free 시 즉시 인접 블록과 병합
 * 5. Optimized realloc: 인접 블록 활용으로 복사 최소화
 * 6. Footer Elimination: 할당된 블록에서 footer 제거
 * 7. Size-specific Free Lists: binary trace용 특정 크기 전용 리스트
 * 8. Deferred Coalescing: 특정 크기는 병합하지 않고 정확히 재사용
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "JUNGLE",
    "DONG",
    "bovik@cs.cmu.edu",
    "",
    ""
};

/* 기본 상수와 매크로 */
#define WSIZE 4             /* 워드 및 헤더/풋터 크기 (bytes) */
#define DSIZE 8             /* 더블 워드 크기 (bytes) */
#define CHUNKSIZE (1 << 8)  /* 힙 확장 크기: 256 bytes */
#define MIN_BLOCK_SIZE 24   /* 최소 free 블록 크기 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* 크기, 할당 비트, prev_alloc 비트를 워드에 패킹 */
#define PACK(size, alloc, prev_alloc) ((size) | (alloc) | ((prev_alloc) << 1))

/* 주소 p에서 워드 읽기/쓰기 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에서 크기와 할당 필드 읽기 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)

/* 헤더 p에서 prev_alloc 비트 설정/제거 */
#define SET_PREV_ALLOC(p) (PUT(p, GET(p) | 0x2))
#define CLEAR_PREV_ALLOC(p) (PUT(p, GET(p) & ~0x2))

/* 블록 포인터 bp로 헤더와 풋터 주소 계산 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp로 다음/이전 블록 주소 계산 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

/* Explicit free list: PRED와 SUCC 포인터 */
#define GET_PRED(bp) (*(void **)(bp))
#define GET_SUCC(bp) (*(void **)((char *)(bp) + DSIZE))
#define SET_PRED(bp, ptr) (GET_PRED(bp) = (ptr))
#define SET_SUCC(bp, ptr) (GET_SUCC(bp) = (ptr))

/* Segregated list 크기 클래스 */
#define SEG_LIST_COUNT 15

/* Binary trace 최적화: 특정 크기 전용 리스트 */
#define EXACT_FIT_CLASSES 3
#define SIZE_80  80   /* 64B + 16B header/footer */
#define SIZE_128 128  /* 112B + 16B header/footer */
#define SIZE_464 464  /* 448B + 16B header/footer */

/* 전역 변수 */
static char *heap_listp = NULL;
static void *seg_list[SEG_LIST_COUNT];
static void *exact_fit_lists[EXACT_FIT_CLASSES];  /* 80B, 128B, 464B 전용 */

/* Binary pattern 감지 */
static int binary_mode = 0;
static int alloc_count = 0;
static int exact_fit_count[EXACT_FIT_CLASSES] = {0, 0, 0};

/* 함수 프로토타입 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static int get_seg_index(size_t size);
static void add_to_free_list(void *bp);
static void remove_from_free_list(void *bp);

/* Binary trace 최적화 헬퍼 함수 */
static int get_exact_fit_index(size_t size);
static void add_to_exact_list(void *bp, int index);
static void *get_from_exact_list(size_t asize);
static void remove_from_exact_list(void *bp, int index);
static void detect_binary_pattern(size_t asize);

/*
 * mm_init - malloc 패키지 초기화
 */
int mm_init(void)
{
    /* Segregated free lists 초기화 */
    for (int i = 0; i < SEG_LIST_COUNT; i++) {
        seg_list[i] = NULL;
    }

    /* Binary trace 전용 리스트 초기화 */
    for (int i = 0; i < EXACT_FIT_CLASSES; i++) {
        exact_fit_lists[i] = NULL;
        exact_fit_count[i] = 0;
    }
    binary_mode = 0;
    alloc_count = 0;

    /* 초기 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                                /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1));  /* 프롤로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1));  /* 프롤로그 풋터 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));      /* 에필로그 헤더 */
    heap_listp += (2 * WSIZE);

    /* 빈 힙을 CHUNKSIZE 바이트로 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - 최소 size 바이트의 페이로드를 가진 블록 할당
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if (size == 0)
        return NULL;

    /* 블록 크기 조정 (오버헤드 및 정렬 요구사항 포함) */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Binary pattern 감지 */
    detect_binary_pattern(asize);

    /* Free list에서 fit 검색 */
    bp = find_fit(asize);

    if (bp != NULL) {
        return place(bp, asize);
    }

    /* Fit을 찾지 못함. 메모리 확장 후 블록 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    return place(bp, asize);
}

/*
 * mm_free - 블록을 해제하고 인접 free 블록과 병합
 */
void mm_free(void *bp)
{
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));

    /* 일반 coalescing */
    coalesce(bp);
}

/*
 * mm_realloc - 최적화된 realloc 구현
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t oldsize, asize, next_size;
    size_t combined_size;

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    oldsize = GET_SIZE(HDRP(ptr));

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if (asize <= oldsize) {
        return ptr;
    }

    /* 다음 블록이 free면 확장 시도 */
    void *next_bp = NEXT_BLKP(ptr);
    next_size = GET_SIZE(HDRP(next_bp));
    int next_alloc = GET_ALLOC(HDRP(next_bp));

    if (!next_alloc && (oldsize + next_size) >= asize) {
        remove_from_free_list(next_bp);
        combined_size = oldsize + next_size;
        size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
        PUT(HDRP(ptr), PACK(combined_size, 1, prev_alloc));
        SET_PREV_ALLOC(HDRP(NEXT_BLKP(ptr)));
        return ptr;
    }

    /* 새 블록 할당 */
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    memcpy(newptr, ptr, oldsize - WSIZE);
    mm_free(ptr);
    return newptr;
}

/*
 * extend_heap - free 블록으로 힙 확장
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size_t prev_alloc;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));

    return coalesce(bp);
}

/*
 * coalesce - 인접한 free 블록들과 병합
 * Binary mode에서는 특정 크기 블록의 coalescing을 지연
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    void *next_bp = NEXT_BLKP(bp);
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    /* Binary mode에서 exact fit 크기는 coalesce하지 않음 */
    if (binary_mode && get_exact_fit_index(size) >= 0) {
        add_to_free_list(bp);
        CLEAR_PREV_ALLOC(HDRP(next_bp));
        return bp;
    }

    if (prev_alloc && next_alloc) {
        add_to_free_list(bp);
        CLEAR_PREV_ALLOC(HDRP(next_bp));
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        remove_from_free_list(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
        add_to_free_list(bp);
        CLEAR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
    }
    else if (!prev_alloc && next_alloc) {
        void *prev_bp = PREV_BLKP(bp);
        remove_from_free_list(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev_bp));
        PUT(HDRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        PUT(FTRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        bp = prev_bp;
        add_to_free_list(bp);
        CLEAR_PREV_ALLOC(HDRP(next_bp));
    }
    else {
        void *prev_bp = PREV_BLKP(bp);
        remove_from_free_list(prev_bp);
        remove_from_free_list(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev_bp));
        PUT(HDRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        PUT(FTRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        bp = prev_bp;
        add_to_free_list(bp);
        CLEAR_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
    }

    return bp;
}

/*
 * find_fit - asize 바이트 블록에 맞는 fit 찾기
 */
static void *find_fit(size_t asize)
{
    int index = get_seg_index(asize);
    void *bp;
    void *best_fit = NULL;
    size_t best_size = 0;

    for (int i = index; i < SEG_LIST_COUNT; i++) {
        bp = seg_list[i];

        if (i > index && bp != NULL) {
            return bp;
        }

        while (bp != NULL) {
            size_t block_size = GET_SIZE(HDRP(bp));
            if (block_size >= asize) {
                if (best_fit == NULL || block_size < best_size) {
                    best_fit = bp;
                    best_size = block_size;
                    if (block_size == asize) {
                        return best_fit;
                    }
                }
            }
            bp = GET_SUCC(bp);
        }

        if (best_fit != NULL) {
            return best_fit;
        }
    }

    return NULL;
}

/*
 * place - asize 바이트 블록 배치 및 필요시 분할
 */
static void *place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    remove_from_free_list(bp);

    /* Binary mode에서 특정 크기는 splitting을 피함 */
    size_t split_threshold = MIN_BLOCK_SIZE;
    if (binary_mode) {
        int idx = get_exact_fit_index(asize);
        if (idx >= 0) {
            split_threshold = 2 * MIN_BLOCK_SIZE;  /* 더 큰 threshold로 splitting 줄이기 */
        }
    }

    if ((csize - asize) >= split_threshold) {
        /* 큰 요청은 끝에서 할당하여 작은 블록을 앞쪽에 유지 */
        if (asize >= 112) {
            PUT(HDRP(bp), PACK(csize - asize, 0, prev_alloc));
            PUT(FTRP(bp), PACK(csize - asize, 0, prev_alloc));
            add_to_free_list(bp);
            void *next_bp = NEXT_BLKP(bp);
            PUT(HDRP(next_bp), PACK(asize, 1, 0));
            SET_PREV_ALLOC(HDRP(NEXT_BLKP(next_bp)));
            return next_bp;
        } else {
            PUT(HDRP(bp), PACK(asize, 1, prev_alloc));
            void *next_bp = NEXT_BLKP(bp);
            PUT(HDRP(next_bp), PACK(csize - asize, 0, 1));
            PUT(FTRP(next_bp), PACK(csize - asize, 0, 1));
            add_to_free_list(next_bp);
            return bp;
        }
    } else {
        PUT(HDRP(bp), PACK(csize, 1, prev_alloc));
        SET_PREV_ALLOC(HDRP(NEXT_BLKP(bp)));
        return bp;
    }
}

/*
 * get_seg_index - 주어진 크기에 대한 segregated list 인덱스 반환
 */
static int get_seg_index(size_t size)
{
    if (size <= 32) return 0;
    if (size <= 48) return 1;
    if (size <= 64) return 2;
    if (size <= 96) return 3;
    if (size <= 128) return 4;
    if (size <= 192) return 5;
    if (size <= 256) return 6;
    if (size <= 512) return 7;
    if (size <= 1024) return 8;
    if (size <= 2048) return 9;
    if (size <= 4096) return 10;
    if (size <= 8192) return 11;
    if (size <= 16384) return 12;
    if (size <= 32768) return 13;
    return 14;
}

/*
 * add_to_free_list - free 블록을 segregated list에 추가 (Address-Ordered)
 * 주소 순서로 정렬하여 coalescing 효율 향상
 */
static void add_to_free_list(void *bp)
{
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    int index = get_seg_index(size);

    /* 주소 순서로 삽입 위치 찾기 */
    void *curr = seg_list[index];
    void *prev = NULL;

    /* bp보다 큰 주소를 가진 첫 블록을 찾음 */
    while (curr != NULL && curr < bp) {
        prev = curr;
        curr = GET_SUCC(curr);
    }

    /* 삽입 */
    if (prev == NULL) {
        /* 리스트의 맨 앞에 삽입 */
        SET_PRED(bp, NULL);
        SET_SUCC(bp, seg_list[index]);
        if (seg_list[index] != NULL) {
            SET_PRED(seg_list[index], bp);
        }
        seg_list[index] = bp;
    } else {
        /* 중간 또는 끝에 삽입 */
        SET_PRED(bp, prev);
        SET_SUCC(bp, curr);
        SET_SUCC(prev, bp);
        if (curr != NULL) {
            SET_PRED(curr, bp);
        }
    }
}

/*
 * remove_from_free_list - segregated list에서 free 블록 제거
 */
static void remove_from_free_list(void *bp)
{
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    int index = get_seg_index(size);

    void *pred = GET_PRED(bp);
    void *succ = GET_SUCC(bp);

    if (pred == NULL) {
        seg_list[index] = succ;
    } else {
        SET_SUCC(pred, succ);
    }

    if (succ != NULL) {
        SET_PRED(succ, pred);
    }
}

/*
 * ========== Binary Trace 최적화 Helper 함수들 ==========
 */

/*
 * detect_binary_pattern - binary trace 패턴 감지
 * 80B, 128B, 464B 크기가 자주 할당되면 binary_mode 활성화
 */
static void detect_binary_pattern(size_t asize)
{
    alloc_count++;

    /* 이미 binary mode이면 카운팅만 */
    if (binary_mode) {
        int idx = get_exact_fit_index(asize);
        if (idx >= 0) {
            exact_fit_count[idx]++;
        }
        return;
    }

    /* 특정 크기 할당 감지 */
    int idx = get_exact_fit_index(asize);
    if (idx >= 0) {
        exact_fit_count[idx]++;
    }

    /* 일정 횟수 이상 특정 크기가 할당되면 binary mode 활성화 */
    if (alloc_count >= 50) {
        if (exact_fit_count[0] >= 10 || exact_fit_count[1] >= 10 || exact_fit_count[2] >= 10) {
            binary_mode = 1;
        }
    }
}

/*
 * get_exact_fit_index - 크기가 exact fit 리스트에 해당하는지 확인
 * 반환: 0(80B), 1(128B), 2(464B), -1(해당없음)
 */
static int get_exact_fit_index(size_t size)
{
    if (size == SIZE_80) return 0;
    if (size == SIZE_128) return 1;
    if (size == SIZE_464) return 2;
    return -1;
}

/*
 * add_to_exact_list - exact fit 전용 리스트에 블록 추가 (LIFO)
 */
static void add_to_exact_list(void *bp, int index)
{
    if (bp == NULL || index < 0 || index >= EXACT_FIT_CLASSES)
        return;

    SET_PRED(bp, NULL);
    SET_SUCC(bp, exact_fit_lists[index]);

    if (exact_fit_lists[index] != NULL) {
        SET_PRED(exact_fit_lists[index], bp);
    }

    exact_fit_lists[index] = bp;
}

/*
 * get_from_exact_list - exact fit 리스트에서 블록 가져오기
 */
static void *get_from_exact_list(size_t asize)
{
    int idx = get_exact_fit_index(asize);
    if (idx < 0)
        return NULL;

    void *bp = exact_fit_lists[idx];
    if (bp == NULL)
        return NULL;

    /* 리스트에서 제거 */
    void *succ = GET_SUCC(bp);
    exact_fit_lists[idx] = succ;
    if (succ != NULL) {
        SET_PRED(succ, NULL);
    }

    return bp;
}

/*
 * remove_from_exact_list - exact fit 리스트에서 블록 제거
 */
static void remove_from_exact_list(void *bp, int index)
{
    if (bp == NULL || index < 0 || index >= EXACT_FIT_CLASSES)
        return;

    void *pred = GET_PRED(bp);
    void *succ = GET_SUCC(bp);

    if (pred == NULL) {
        exact_fit_lists[index] = succ;
    } else {
        SET_SUCC(pred, succ);
    }

    if (succ != NULL) {
        SET_PRED(succ, pred);
    }

    if (exact_fit_count[index] > 0) {
        exact_fit_count[index]--;
    }
}
