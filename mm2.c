#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 *
 * NOTE TO STUDENTS: 무언가를 하기 전에 다음 구조체에 팀 정보를 제공하십시오.
 ********************************************************/
team_t team = {
    /* Team name */
    "Green 2 team",
    /* First member's full name */
    "kim tae young",
    /* First member's email address */
    "markdj9205@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/*
1<<12는 비트 연산자인 시프트(Shift) 연산자를 사용하여, 2의 12승을 계산하는 방법입니다.
<<는 좌측 시프트 연산자로, 왼쪽의 피연산자(1)를 2진수로 표현했을 때 각 비트를 지정한 수만큼 왼쪽으로 이동시키는 연산을 수행합니다.
따라서 1<<12는 0001을 왼쪽으로 12비트 이동시켜서 0001 0000 0000 0000을 만드는 것이며, 이진수로 표현하면 2의 12승인 4096이 됩니다.
따라서 #define CHUNKSIZE (1<<12)는 CHUNKSIZE를 4096으로 정의하는 것입니다.
*/
/* start */
/* 가용 리스트 조작을 위한 기본 상수 및 매크로 정의 */
/* 기본 상수와 매크로*/
#define WSIZE 4     /*워드 크기*/
#define DSIZE 8     /*더블 워드 크기*/
#define CHUNKSIZE (1<<12)/*초기 가용 블록과 힙 확장을 위한 기본 크기*/
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/*크기와 할당된 비트를 하나의 워드(word)에 패킹
크기와 할당 비트를 통합해 헤더와 풋터에 저장할 수 있는 값을 리턴한다.*/
#define PACK(size, alloc) ((size) | (alloc))
/*
p는 대개 (void*) 이므로 직접적으로 역참조가 불가능 하다
(unsigned = 부호 비트를 제거해 저장 가능한 양수 범위를 두배로 늘이는 역할)
*/
/*인자 p가 참조하는 워드를 읽어서 리턴한다.*/
#define GET(p)          (*(unsigned int *)(p))
/*인자 p가 가리키는 워드에 val을 저장한다.*/
#define PUT(p, val)     (*(unsigned int *)(p) = (val))
/*p 주소에서 크기와 할당된 필드를 읽어들입니다.
각각 주소 p에 있는 헤더 또는 풋터의 size를 리턴한다*/
#define GET_SIZE(p)     (GET(p) & ~0x7)
/*p 주소에서 크기와 할당된 필드를 읽어들입니다.
각각 주소 p에 있는 헤더 또는 풋터의 할당 비트를 리턴한다*/
#define GET_ALLOC(p)    (GET(p) & 0x1)
/*주어진 블록 포인터 bp에 대해, 해당 블록의 헤더의 주소를 계산*/
#define HDRP(bp)        ((char *)(bp) - WSIZE)
/*주어진 블록 포인터 bp에 대해, 해당 블록의 풋터의 주소를 계산*/
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/*주어진 블록 포인터(bp)를 이용하여 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/*주어진 블록 포인터(bp)를 이용하여 이전 블록의 주소를 계산*/
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
// implicit
/*  *(GET(PREC_FREEP(bp))) == 다음 가용리스트의 bp //Predecessor  */
#define PREC_FREEP(bp)  (*(void **)(bp))
/* *(GET(SUCC_FREEP(bp))) == 다음 가용리스트의 bp //successor */
#define SUCC_FREEP(bp)  (*(void **)(bp + WSIZE))
void removeBlock(void *bp);
void putFreeBlock(void *bp);
 // 가용리스트의 첫번째 블록을 가리키는 포인터
static void *free_listp;
/* ---------------  */
static void *heap_listp;
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
/* end */
/*
 * mm_init - initialize the malloc package.
 * mm_init - malloc 패키지를 초기화합니다.
 */
int mm_init(void)
{
    /* 최초 가용 블록으로 힙 생성 */
    /*
    초기 빈 힙을 생성합니다
    메모리 시스템(mem_sbrk)에서 4 워드를 가져와서
    빈 가용 리스트를 만들 수 있도록 초기화 한다
    */
    if ((heap_listp = mem_sbrk(6 * WSIZE))==(void*)-1){
        return -1;
    }
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE*2,1));   /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), (int)NULL);   /* 프롤로그 PREC 포인터 NULL로 초기화 */
    PUT(heap_listp + (3 * WSIZE), (int)NULL);   /* 프롤로그 SUCC 포인터 NULL로 초기화 */
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE*2,1));   /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0,1));       /* Epilogue header */
    //heap_listp += (3 * DSIZE);
    /* 가용리스트에 블록이 추가될 때 마다 항상 리스트의 제일 앞에 추가될 것이므로
    지금 생성한 프롤로그 블록은 항상 가용리스트의 끝에 위치하게 된다 */
    free_listp = heap_listp + DSIZE; // free_listp 초기화
    /*빈 힙에 CHUNKSIZE 바이트의 빈 블록을 추가*/ // WSIZE -> DISZE 변경 하면 2점오름
    if(extend_heap(CHUNKSIZE/DSIZE)== NULL){
        return -1;
    }
    return 0;
}
/* 새 가용 블록으로 힙 확장하기 */
static void *extend_heap(size_t words)
{
    char * bp;
    size_t size;
    /*요청한 크기를 인접 2워드의 배수로 반올림하며,
    그 후에 메모리 시스템으로부터 추가적인 힙 공간을 요청*/
    /*정렬을 유지하기 위해 words 수를 짝수로 할당*/
    size = (words % 2) ? (words + 1) * DSIZE : words * DSIZE; // WSIZE -> DSIZE 로 바꾸면 2점 오름
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    /*프리 블록의 헤더(header)와 푸터(footer) 및 에필로그(epilogue) 헤더를 초기화*/
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */ /* 새 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0, 1));    /* New epilogue header */ /* 새 에필로그 블록 헤더*/
    /*이전 블록이 프리 블록(free block)인 경우, 병합(coalesce)을 수행*/
    return coalesce(bp);
}
/*
size 바이트의 메모리 블록을 요청할떄 추가적인 요청들을 체크한 후에
할당기는 요청한 블록 크기를 조절해서 헤더와 풋터를 위한 공간을 확보하고,
 더블 워드 요건을 만족시킨다.
 */
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * mm_malloc - 블록을 할당하기 위해 brk 포인터를 증가시킵니다
 *      항상 정렬의 배수인 크기의 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    /* 가용 리스트에서 블록할당 하기 */
    size_t asize;
    size_t extendsize;
    char *bp;
    if(size == 0){
        return NULL;
    }
    /*
    최소 16 바이트 크기의 블록을 구성한다
    : 8 바이트는 정렬 요건을 만족시키기 위해 추가적인
    8바이트는 헤더와 풋터 오버헤드를 위해 8바이트를 넘기는 요청에 대해서는
    else 문에 구성 처럼 일반적인 규칙은 오버헤드 바이트를 추가하고,
    인접 8의 배수로 반올림 하는 것이다.
    */
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    /*
    할당기가 요청한 크기를 조정한 후에 적절한 가용 블록을 가용 리스트에서 검색한다
    만일 맞는 블록을 찾으면 할당기는 요청한 블록을 배치하고(if문 조건문 안에서 find_fit() 함수 부분),
    옵션으로 초과부분을 분할라고(place 함수 부분), 새롭게 할당한 블록을 리턴한다.
    */
    if((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    /*
    할당기가 맞는 블록을 찾지 못하면, 힙을 새로운 가용 블록으로 확장하고,
    요청한 블록을 이 새 가용 블록에 배치하고, 필요한 경우에 블록을 분할하며(place 함수 부분),
    이후에 새롭게 할당한 블록의 포인터를 리턴한다.
    */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/DSIZE)) == NULL){ // WIZE -> DSIZE 변경 하면 2점 오름
        return NULL;
    }
    place(bp,asize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 * mm_free - 블록을 해제하면 아무것도 하지 않습니다.
 */
void mm_free(void *bp)
{
    /* 블록을 반환하고 경계 태그 연결을 사용해서
    상수 시간에 인접 가용 블록들과 통합 */
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // 이전 블록이 할당 블록이고, 다음 블록이 가용 블록인 경우
    if (prev_alloc && !next_alloc){
        // 다음 블록을 가용 리스트에서 제거하고, 블록 크기를 합친다
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // 이전 블록이 가용 블록이고, 다음 블록이 할당 블록인 경우
    else if (!prev_alloc && next_alloc){
        // 이전 블록을 가용 리스트에서 제거하고, 블록 크기를 합친다
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // 이전 블록과 다음 블록이 모두 가용 블록인 경우
    else if (!prev_alloc && !next_alloc){
        // 이전 블록과 다음 블록을 가용 리스트에서 제거하고, 블록 크기를 합친다
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    //연결된 블록을 가용리스트에 추가
    putFreeBlock(bp);
    return bp;
}
/*
1. 입력으로 받은 bp 주소를 oldptr에 저장하고,
    새롭게 할당할 메모리 주소를 newptr에 저장합니다.
2. 만약 size가 0이면,
    free 함수를 호출하여 oldptr을 free()하고 NULL을 반환합니다.???
3. bp가 NULL이면,
    malloc 함수를 호출하여 size 크기의 메모리를 할당하고 해당 주소를 반환합니다.
4. newptr이 NULL을 반환하면,
    할당 실패로 처리합니다.
5. 그 외의 경우, oldptr의 크기를 계산하고,
    size와 비교하여 copySize에 저장합니다.
6. newptr로 copySize 만큼 데이터를 복사합니다.
7. oldptr을 free()하고 newptr을 반환합니다. ??
*/
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * mm_realloc - 단순히 mm_malloc과 mm_free를 이용해 구현됩니다.
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copySize;
    //size가 0이면 free와 같음
    if(size == 0){
        mm_free(bp);
        return NULL;
    }
    //bp이 NULL이면 malloc과 같음
    if(bp == NULL){
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);
    if(newptr == NULL){
        return NULL;
    }
    // 복사할 데이터 크기 결정
    copySize = GET_SIZE(HDRP(oldptr));
    if(size < copySize){
        copySize = size;
    }
    // 기존 블록에서 새로운 블록으로 데이터 복사
    memcpy(newptr, oldptr, copySize);
    // 기존 블록 free
    mm_free(oldptr);
    // 새로운 블록 주소 반환
    return newptr;
}
/*
1. 먼저 힙의 첫 번째 블록부터 시작하여 마지막 블록까지 순회합니다.
2. 각 블록을 검사하여 할당되어 있지 않고,
    요청한 크기(asize)보다 크거나 같은 블록을 찾습니다.
3. 적절한 크기의 블록을 찾으면 해당 블록의 주소를 반환하고,
    찾지 못한 경우 NULL을 반환합니다.
*/
/* 동적 메모리 할당 시 메모리 블록을 찾는 함수 */
static void *find_fit(size_t asize)
{
    void *bp;
    // 가용 블록 리스트에서 블록 크기가 asize 이상인 첫 번째 블록을 찾음
    for(bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if((asize <= GET_SIZE(HDRP(bp)))){
            return bp;     // 찾은 블록의 주소 반환
        }
    }
    return NULL; // 적절한 크기의 블록을 찾지 못한 경우 NULL 반환
}
/*
1. 할당 대상 블록의 현재 크기를 csize에 저장합니다.
2. 할당 요청한 크기(asize)와 현재 블록의 크기(csize)를 비교합니다.
3. 남은 공간이 최소 블록 크기보다 크다면 분할 가능한 상황입니다.
    할당 요청한 크기만큼 할당하고, 남은 공간에 새로운 블록 헤더와 풋터를 추가합니다.
4. 남은 공간이 최소 블록 크기보다 작아서 분할이 불가능한 상황입니다.
    할당 대상 블록을 전체 할당합니다.
*/
/* 가용 블록 중에서 요청한 크기(asize)에 따라 적절한 크기의 블록을 할당하는 함수 */
static void place(void *bp, size_t asize)
{
    // 할당 대상 블록의 현재 크기
    size_t csize = GET_SIZE(HDRP(bp));
    // 할당될 블록이니 가용리스트 내부에서 제거해준다.
    removeBlock(bp);
    // 남은 공간이 최소 블록 크기보다 크다면 분할 가능
    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));  // 할당 요청한 크기만큼 할당
        PUT(FTRP(bp), PACK(asize, 1));  // 할당 요청한 크기만큼 할당
        bp = NEXT_BLKP(bp); // bp를 다음 블록으로 이동
        PUT(HDRP(bp),PACK(csize - asize, 0)); // 남은 공간에 새로운 블록 헤더 추가
        PUT(FTRP(bp),PACK(csize - asize, 0)); // 남은 공간에 새로운 블록 풋터 추가
        putFreeBlock(bp); // 가용리스트 첫번째에 분할된 블럭을 넣는다.
    }
    // 남은 공간이 최소 블록 크기보다 작아서 분할 불가능
    else{
        PUT(HDRP(bp),PACK(csize, 1)); // 할당 대상 블록을 전체 할당
        PUT(FTRP(bp),PACK(csize, 1)); // 할당 대상 블록을 전체 할당
    }
}
/* 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가한다 */
void putFreeBlock(void *bp)
{
    SUCC_FREEP(bp) = free_listp;
    PREC_FREEP(bp) = NULL;
    PREC_FREEP(free_listp) = bp;
    free_listp = bp;
}
/*항상 가용리스트 맨 뒤에 프롤로그 블록이 존재하고 있기 때문에 조건을 간소화할 수 있다.*/
void removeBlock(void *bp)
{
    // 첫번째 블럭을 없앨 때
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    // 앞 뒤 모두 있을 때
    }else{
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
}