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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "2team",
    /* First member's full name */
    "kim tae young",
    /* First member's email address */
    "markdj9205@google.com",
    /* Second member's full name (leave blank if none) */
    "asd",
    /* Second member's email address (leave blank if none) */
    "asd@naver.com"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* Basic constants and macros*/
#define WSIZE 4 /*1개의 word사이즈/*haeder/footer size는 메모리 할당에서 각 할당된 블록 앞과 뒤에 추가되는 데이터 단위를 말한다. 이 데이터는 할당된 블록의 크기,사용 가능 여부, 이전/다음 블록의 위치 등의 정보를 저장한다. 이러한 정보를 헤더와 푸터에 저장하며, 각각의 크기는 구현과 상황에 따라 다를 수 있다.*/
#define DSIZE 8 /*double word size (bytes)*/
#define CHUNKSIZE (1<<12) /*힙의 크기를 확장하여 추가적인 메모리 공간을 할당한다는 의미이다.*/
#define MAX(x,y) ((x) > (y)? (x) : (y))/*x,y 중 큰 값을 가진다.*/
/*size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산) |은 논리합이고 ||은 or 연산을 반환한다.*/
#define PACK(size, alloc) ((size) | (alloc))
/*address p위치에 words를 read와 write를 한다.*/
#define GET(p)           (*(unsigned int *)(p)) /*포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다)을 알 수 있따. 다른 블록을 가리키거나 이동할 때 쓸 수 있다.*/
#define PUT(p, val)      (*(unsigned int *)(p) = (val)) /*블록의 주소를 담는다. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있다.*/
/*address p위치로부터 size를 읽고 field를 할당*/
#define GET_SIZE(p)    (GET(p) & ~0x7) /*~은 역수이기 때문에 11111000이 된다. 비트연산하면 000 앞에 것만 가져올 수 있음. 즉, 헤더에서 블록 size만 가져오겠다는 소리이다.*/
#define GET_ALLOC(p)    (GET(p) & 0x1) /*00000001이 된다. 헤더에서 가용여부만 가져오겠다.*/
/*header와 footer의 주소를 계산*/
#define HDRP(bp)        ((char *)(bp) - WSIZE) /*bp가 어디에 있던 wsize앞에 위치한다.*/
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /*헤더의 끝 지점부터 GETSIZE(블록의 사이즈)만큼 더한 다음 DSIZE 빼는 게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작위치가 된다.*/
/*이전 블록과 다음 불록의 주소를 계산한다.*/
#define NEXT_BLKP(bp)        ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))/*그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동-> 그 다음 블록의 헤더 뒤로 간다)*/
#define PREV_BLKP(bp)        ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))/*그 전 블록의 bp위치로 이동(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동)*/   
static char *heap_listp; /*처음에 쓸 큰 가용블록 힙을 만들어준다.*/
static char *last_bp;
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

/* 
 * mm_init - 이 함수는 할당기를 초기화하고 성공하면 0, 실패면 -1을 리턴한다.
 초기화 하는 과정에는 가용 리스트의 prologue header, footer, epilogue header를 만드는 과정이 포함 된다.
 최소 블록 크기는 16byte로정한다.
 */
/*mm_init함수에 필요한것
*힙을 초기 size 만큼 설정 한다.
*가용리스트에 패딩을 넣어준다.
*가용리스트에 프롤로그 헤더를 넣는다.
*가용리스트에 프롤로그 푸터를 넣는다.
*가용리스트에 에필로그 헤더를 넣는다.
*힙에 블록을 할당하기 위해 사이즈를 적당히 한번 늘린다.
*/
/*처음에 heap을 시작할 때 0부터 시작한다.(힙의 시작점)*/
int mm_init(void)
{
    /*초기에 빈 힙을 만들어준다.*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){ /*old brk에서 4만큼 늘려서 mem brk로 늘림*/
        return -1;
    }    
    PUT(heap_listp, 0); /*블록생성시 넣는 padding을 1 word 크기만큼 생성, heap_list 위치는 맨처음*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /*prologue header생성. pack을 해석하면, 할당할거다(1), DSIZE만큼(8) -> 1 wsize 늘어난 시점부터 pack에서 나온 사이즈를 줄거다*/
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /*prologue footer생성*/    
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /*epilogue block header를 처음에 만든다. 그리고 뒤로 밀리는 형태*/
    heap_listp += (2*WSIZE); /*prologue header와 footer 사이로 포인터를 옮긴다. header 뒤 위치*/

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){ /*extend heap을 통해 시작할 때 한번 heap을 늘려준다. 늘리는 양은 상관없다?*/
        return -1;
    }
    last_bp = (char *)heap_listp;
    return 0; // 완료됬다.
}

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size; /*size+t = unsigned int, 이 함수에서 넣을 size를 하나 만들어줌*/
    /*alignment 유지를 위해 짝수 개수의 words를 allocate*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; /*홀수 인 경우 1이 나온다 따라서 words+1을 해준다.(패딩)*/
    if ((long)(bp = mem_sbrk(size)) == -1) //sbrk로 size를 늘려서 long형으로 만든다. mem_sbrk가 반환되면 bp는 현재 만들어진 블록의 끝에 가있다.
        return NULL; //사이즈를 늘릴 때마다 old brk는 과거의 mem_brk위치로 간다.

    /*free block 헤더와 푸터를 init하고 epilogue 헤더를 init*/
    PUT(HDRP(bp), PACK(size, 0)); //free block header 생성. regular block의 총합 첫번째 부분. 현재 bp 위치의 한 칸 앞에 헤더를 생성.
    PUT(FTRP(bp), PACK(size, 0)); //free block footer 생성. regular block의 총합 마지막 부분
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //블록을 추가 했으니 epiloge header를 새롭게 위치 조정해줌
    /*만약 prev block이 free라면, coalesce하라*/    
    return coalesce(bp); // 처음에는 coalesc를 할게 없지만 함수를 재사용하기 위해 리턴값으로 선언해준다.
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //그 전 블록으로 가서 그 블록의 가용여부를 확인한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //그 뒷 블록의 가용 여부를 확인한다.
    size_t size = GET_SIZE(HDRP(bp)); //현재 블록의 사이즈를 확인다.

    if (prev_alloc && next_alloc){ //[case1] 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
        return bp; //이미 free에서 가용이 되어있으니 여기선 따로 free할 필요가 없다.       
    }
    else if (prev_alloc && !next_alloc){ //[case2] 이전 블록은 할당 상태, 다음 블록은 가용상태인경우->현재 블록은 다음 블록과 통합 됨. &&?
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));// 다음 블록의 헤더를 보고 그 블록의 크기만큼 지금 블록의 사이즈에 추가해준다.
        PUT(HDRP(bp), PACK(size, 0)); //헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); //푸터 갱신
    }

    else if (!prev_alloc && next_alloc){ //[case3] 이전 블록은 가용상태, 다음 블록은 할당 상태->이전 블록은 현재 블록과 통합
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //이전 블록의 헤더를 보고 그 블록의 크리만큼 지금 블록의 사이즈에 추가해준다.
        PUT(FTRP(bp), PACK(size, 0)); //푸터에 먼저 조정하려는 크기로 상태를 변경한다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //현재 헤더에서 그 앞블록의 헤더 위치로 이동한 뒤 조정한 사이즈를 넣는다.
        bp = PREV_BLKP(bp); //bp를 그 앞블록의 헤더로 이동(늘린 블록의 헤더이므로)
    }

    else { //[case4] 이전 블로과 다음 블록 모두 가용상태. 이전, 현재, 다음의 블록 모두 하나의 가용블록으로 만들어준다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈를 늘린다.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 헤더부터 앞으로 가서 사이즈를 넣고,
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 푸터를 뒤로 가서 사이즈를 넣는다.
        bp = PREV_BLKP(bp); // 그 전 블록으로 이동.
    }
    last_bp = bp;
    return bp; // 케이스 4개 중 적용된 것으로 bp리턴
}


static void *find_fit(size_t asize) 
{//first fit 검색을 수행
    char *bp = last_bp;
    // 최근에 할당된 블록을 기준으로 다음 블록 검색
        for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
                last_bp = bp;
                return bp;
            }
    }
    // 메모리 블록의 처음부터 마지막 할당된 블록까지 검색
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}


/*가용 리스트에서 블록 할당하기*/
void *mm_malloc(size_t size)
{
    size_t asize;/*블록 사이즈 조정*/
    size_t extendsize;/*heap에 맞는 fit이 없으면 확장하기 위한 사이즈*/
    char *bp;

    if (size == 0) //거짓 요청에 대해서는 무시한다(size가 0이라는 것은 할당할 필요가 없다는 것이므로)
        return NULL;

    if (size <= DSIZE) //overhead, alignment 요청을 포함해 블록 사이즈를 조정
        asize = 2*DSIZE; //헤더와 푸터를 포함해서 블록사이즈를 다시 조정해야되니까 DISIZE의 2배를 준다.
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);//size보다 클 때, 블록이 가질 수 있는 크기 중에 최적화된 크기로 조정
    /*fit에 맞는 free리스트를 찾는다*/
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; //place를 마친 블록의 위치를 리턴한다.       
    }    
    // 위에서 맞는 블록이 없다면 메모리를 더 가져와서 block을 위치시킨다.
    extendsize = MAX(asize, CHUNKSIZE);  //asize와 CHUNKSIZE(처음에 세팅한 사이즈)중 더 큰것을 넣는다.
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
    // 단위 블록 수를 넣어 주기 위해서 extendsize/wsize로 나누어 준다.
        return NULL;
    }    
    place(bp, asize); //확장된 상태에서 asize를 넣어라
    return bp;        
}


//블록을 반환하고 경계 태그 연결사용
void mm_free(void *bp)
{
    //어느 시점에 있는 bp를 인자로 받는다.
    size_t size = GET_SIZE(HDRP(bp));// 얼만큼 free해야 하는지
    PUT(HDRP(bp), PACK(size, 0)); // header, footer들을 free시킨다. 가용상태로 만들어준다.
    PUT(FTRP(bp), PACK(size, 0)); 
    coalesce(bp);
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
// 	return NULL;
//     else {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr))-DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}



/*힙을 확장하는 경우 가용블록이 생기게 된다. 가용 블록이 생긴 시점에서 현재 주변에 가용 블록이 있는 지 살피고 합칠수 있는 블록은 합쳐야한다.
합치지 않은 경우 false fragmentation문제가 발생하게 된다.*/


/*새 가용 블록으로 힙 확장*/


static void place(void *bp, size_t asize) //들어갈 위치를 포인터로 받는다.(find fit에서 찾은 bp) 크기는 asize
{//요청한 블록을가욕 블록의 시장 부분에 배치, 나머지 부분의 크기가 최소 블록 크기와 같거나 큰경우에만 분할하는 함수
    size_t csize = GET_SIZE(HDRP(bp));//현재 블록사이즈

    if ((csize - asize) >= (2*DSIZE)){ //현재 블록 사이즈안에서 asize를 넣어도 2*Dsize, 남는 경우 
        PUT(HDRP(bp), PACK(asize, 1)); //헤더위치에 asize만큼 넣고 1로 상태변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈로 갱신
        PUT(FTRP(bp), PACK(asize, 1)); //푸터의 위치도 변경
        bp = NEXT_BLKP(bp); //regular block만큼 하나 이동해서 bp위치 갱신
        PUT(HDRP(bp), PACK(csize-asize, 0)); //나머지 블록은 다 가용하다라는 것을 다음 헤어에 표신
        PUT(FTRP(bp), PACK(csize-asize, 0)); //푸터에도 표시
    }
    else {
            PUT(HDRP(bp), PACK(csize, 1)); //위의 조건이 아닌경우 asize만 csize에 들어갈 수 있다.
            PUT(FTRP(bp), PACK(csize, 1));
    }
}