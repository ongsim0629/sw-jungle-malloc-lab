/*
first fit을 이용해서 구현한 explicit 가용 리스트
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "team 6",
    /* First member's full name */
    "subin shin",
    /* First member's email address */
    "s1_1v@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// 기존 매크로들
// 싱글워드(4바이트)로 정렬할건지, 더블워드로 정렬할건지 설정해주기
#define ALIGNMENT 8

// 정렬 조건에 맞춰서 반올림 혹은 올림해준다.
// ALIGNMENT의 경계에 맞춰서 size를 ALIGNMENT의 배수로 만드는 것을 목표로한다.
// 예를 들어서 size 5, ALIGNMENT 8이었으면
// 5 + 7 => 12 그리고 비트마스킹 12 & ~0x7를 통해서 -> 8로 바뀐다.
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// size_t의 크기를 바이트 단위로 측정하고 위의 매크로로 사이즈 조정한다!
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// 기존 매크로들

// implicit 할당기 제작을 위한 교재 수록 매크로들
#define WSIZE 4
#define DSIZE 8
// 2^12 -> 할당기가 시스템으로부터 요청하는 메모리의 최소 단위
// 부족하면 이제 추가 메모리 요청할 거임 (최대 MAX_HEAP (20*(1<<20)) 까지 늘리기 가능)
// 메모리 늘릴 때도 이 chunksize를 단위로 늘어남
#define CHUNKSIZE (1<<10)

#define MAX(x, y) ((x) > (y)? (x):(y))

// 헤더랑 풋터에 넣을 값 리턴해줌 
// 블록 크기(size)랑 할당 여부(alloc) or 연산을 통해서!
#define PACK(size, alloc) ((size) | (alloc))

// p가 가리키는 주소에 unsigned int -> 4바이트 크기 만큼 역참조 해서 접근
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// p 포인터를 통해서 그 값을 받아온 다음에 -> 거기에 and 연산으로 사이즈와 할당 여부만 뽑읍 
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp는 일반적으로 페이로드의 시작 위치를 가리킴    
// 포인터가 char* 형이면 그 만큼의 바이트 연산한다고 생각하기
#define HDRP(bp) ((char *)(bp) - WSIZE)
// GET_SIZE로 받아온 크기에는 헤더+ 페이로드 + 푸터의 크기임 따라서 헤더 + 푸터인 8을 빼주어야지 푸터의 시작 위치임
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

// 다음 블록 혹은 이전 블록의 포인터 얻기!
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// implicit 할당기 제작을 위한 교재 수록 매크로들

// 이전 가용 블록의 포인터를 얻는 매크로
#define PREV_FREEP(bp) (*(void **)(bp))

// 다음 가용 블록의 포인터를 얻는 매크로
#define NEXT_FREEP(bp) (*(void **)((char *)(bp) + WSIZE))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

//연결 리스트의 시작을 가리키는 포인터
static char *root;

// 할당기 초기화 하기 -> 초기 가용 리스트 ㄱㄱ
int mm_init(void)
{
    // 4바이트 6개 -> 프롤로그 2개, 에필로그 1개, 패딩 1개 + 포인터 2개
    // heap_list가 뭔가 많이 관여하지 않는 것 같아서 그냥 그걸 root로 써보면 어떤지 -> 일단 함 해봄
    if((root = mem_sbrk(6*WSIZE)) == (void *)-1) 
        return -1;

    // 패딩을 써야지 실제 블록들을 8의 배수로 할 수 있다                
    PUT(root, 0);
    // 프롤 헤더                         
    PUT(root + (1*WSIZE), PACK(2*DSIZE,1)); 
    // prev 포인터
    PUT(root + (2*WSIZE), NULL); 
    // next 포인터
    PUT(root + (3*WSIZE), NULL);
    // 프롤 푸터
    PUT(root + (4*WSIZE), PACK(2*DSIZE,1));
    // 에필 헤더
    PUT(root + (5*WSIZE), PACK(0,1));

    // root의 prev 가리킬 수 있도록 함
    root += (2*WSIZE);

    // 지금은 진심 초기화니까 -> malloc으로 동적 할당할 공간이 없응게 만들어줘야지
    // 얼만큼 추가 공간 만들어주냐면 1024 워드 만큼의 추가 공간 확보
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

// 초기화 하고 나서 혹은 적당한 fit을 찾지 못했을 때 호출해서
// word (주의 !! 단위 word임) 크기 만큼 힙 영역을 늘리게 해주는 함수이다
static void *extend_heap(size_t words){
    // 바이트 단위로 접근 -> 증감 or 접근하려고
    char *bp;
    // 증가 시킬 힙 영역의 사이즈 (바이트 단위)
    size_t size;

    // 8의 배수만큼 힙을 할당해주고 싶으면 size는 짝수로만 가능하다
    // 왜냐면 더블 워드니까!!!!!!!!
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // size 만큼 지금 힙 크기 늘려준 거고 
    // bp에는 이전의 brk -> 확장된 메모리의 시작 주소이다
    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    // 헤더랑 푸터는 같은 값 넣어주기 -> 사이즈랑 할당여부
    // 지금 늘린 힙은 사용하지 않았으므로 0으로 초기화해준다.
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size, 0));
    // 새로운 에필로그 헤더 : 항상 사이즈는 0, allocate는 1
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    // 만약 주위의 블록이 가용 블록이라면 연결하고, 통합된 블록의 블록 포인터를 리턴해준다
    return coalesce(bp);
}

// 해제된 블록의 prev와 next는 더 이상 연결 리스트에 필요하지 않기 때문에 그 값을 수정할 필요가 없고,
// 해제할 블록의 앞과 뒤만 신경쓰면 된다.
static void *disconnect_linked_list(void *bp){
    // 내가 스택 맨 위였으면
    if (bp == root) {
      PREV_FREEP(NEXT_FREEP(bp)) = NULL;
      root = NEXT_FREEP(bp);
    }
    // 내가 스택 중간이었다면
    else {
        NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
        PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    }
}

// 무조건 bp1이 메모리상 앞에 있는 애임 -> 그렇게 전해주니까
static void *disconnect_two_block(void *bp1, void *bp2) {
    // 첫 번째 블록 bp1이 root이고, 두 블록이 연결된 경우
    if (bp1 == root && NEXT_FREEP(bp1) == bp2) {
        if (NEXT_FREEP(bp2) != NULL) {
            // bp2가 다음 블록을 가리키고 있을 때, 그 다음 블록의 PREV 포인터를 NULL로 설정
            PREV_FREEP(NEXT_FREEP(bp2)) = NULL;
        }
        // root를 bp2의 다음 블록으로 갱신
        root = NEXT_FREEP(bp2);
    }
    // 첫 번째 블록 bp1이 root이고, 두 블록이 직접 연결되어 있지 않은 경우
    else if (bp1 == root && NEXT_FREEP(bp1) != bp2) {
        if (NEXT_FREEP(bp1) != NULL) {
            // bp1의 다음 블록의 PREV 포인터를 NULL로 설정
            PREV_FREEP(NEXT_FREEP(bp1)) = NULL;
        }
        // root를 bp1의 다음 블록으로 갱신
        root = NEXT_FREEP(bp1);
        // bp2와 그 다음 블록 사이의 연결을 해제
        if (NEXT_FREEP(bp2) != NULL) {
            PREV_FREEP(NEXT_FREEP(bp2)) = PREV_FREEP(bp2);
        }
        if (PREV_FREEP(bp2) != NULL) {
            NEXT_FREEP(PREV_FREEP(bp2)) = NEXT_FREEP(bp2);
        }
    }
    // bp1이 root가 아니고 두 블록이 연결된 경우
    else if (bp1 != root && NEXT_FREEP(bp1) == bp2) {
        if (NEXT_FREEP(bp2) != NULL) {
            PREV_FREEP(NEXT_FREEP(bp2)) = PREV_FREEP(bp1);
        }
        if (PREV_FREEP(bp1) != NULL) {
            NEXT_FREEP(PREV_FREEP(bp1)) = NEXT_FREEP(bp2);
        }
    }
    // bp1이 root가 아니고 두 블록이 직접 연결되어 있지 않은 경우
    else {
        if (NEXT_FREEP(bp1) != NULL) {
            PREV_FREEP(NEXT_FREEP(bp1)) = PREV_FREEP(bp1);
        }
        if (PREV_FREEP(bp1) != NULL) {
            NEXT_FREEP(PREV_FREEP(bp1)) = NEXT_FREEP(bp1);
        }
        if (NEXT_FREEP(bp2) != NULL) {
            PREV_FREEP(NEXT_FREEP(bp2)) = PREV_FREEP(bp2);
        }
        if (PREV_FREEP(bp2) != NULL) {
            NEXT_FREEP(PREV_FREEP(bp2)) = NEXT_FREEP(bp2);
        }
    }
    return NULL;
}

// bp를 링크드 리스트에 넣어주고 root로 바꾸는 함수!
static void extend_linked_list(void *bp){
    // 얘가 스택 제일 위의 값이므로
    PREV_FREEP(bp) = NULL;
    // root => 원래 스택 제일 위 값
    NEXT_FREEP(bp) = root;
    // 원래 스택 제일 위의 값의 prev도 없데이트 해주고
    if (root != NULL) {
        PREV_FREEP(root) = bp;
    }
    // 이제 root는 마지막으로 가용처리된 bp인거임~~~
    root = bp;
}

// 앞 뒤 블록 확인하고 가용 상태면 통합 해준 다음에
// 통합된 블록을!!! 연결 리스트에 추가할 수 있게 그 블록을 연결 리스트 추가 함수에 넘겨주는 역할
static void *coalesce(void *bp){
    // 현재 블록의 이전 블록의 푸터로부터 가용, 할당 정보 꿍쳐오기
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 현재 블록의 다음 블록의 헤더로부터 가용, 할당 정보 꿍쳐오기
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 bp가 있는 블록의 사이즈 -> 블록 통합하면 바꿔줘야함 
    size_t size = GET_SIZE(HDRP(bp));

    // 첫 번째 경우: 앞 뒤 둘 다 할당된 상태
    // 그럼 그냥 지금 블록만 연결 리스트의 맨 앞에 추가
    // 그냥 지금 bp에서 뭐 수정할거 없다!
    if (prev_alloc == 1 && next_alloc == 1){
    }

    // 두 번째 경우 : 뒤 블록만 가용 상태
    // 지금 블럭에 뒤 블록까지 연장한 블록을 연결 리스트에 맨 앞에 추가해준다
    // 뒤 블록은 그럼 연결리스트 어딘가에 저장되어있었을테니까 그 연결 끊어주는 과정도 필요하다 -> disconnect_linked_list에서 분담하기
    // 현재 bp에 대한 수정은 필요없음!
    else if (prev_alloc == 1 && next_alloc == 0){
        disconnect_linked_list(NEXT_BLKP(bp));
        // 지금 사이즈에 다음 블록의 사이즈 더해서 사이즈 업데이트
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 현재 블록의 헤더에 업데이트된 사이즈와 가용 표시
        PUT(HDRP(bp), PACK(size, 0));
        // 현재 블록의 푸터에 업데이트된 사이즈와 가용 표시
        // 헤더가 먼저 업데이트 되었으므로 알맞는 사이즈의 푸터에 저장되는거임 걱정하지말자
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 세 번째 경우 : 앞 블록만 가용 상태
    // 지금 블럭에 앞 블록까지 연장한 블록을 연결 리스트 맨 앞에 추가해준다.
    // 앞 블록은 그럼 연결리스트 어딘가에 저장되어있었을테니까 그 연결 끊어주는 과정도 필요하다 -> disconnect_linked_list에서 분담하기
    // bp의 위치를 앞 블록의 bp로 이동시켜주기!
    else if (prev_alloc == 0 && next_alloc == 1){
        disconnect_linked_list(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        // bp 업데이트
        bp = (PREV_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 네 번째 경우 : 앞, 뒤 둘 다 가용
    // 지금 블럭에 앞 블록 + 뒷 블록 연장한 블록을 연결 리스트 맨 앞에 추가해준다.
    // 앞 뒤 블록이 연결리스트에 저장되어 있을 테니까 그거 끊어주기 -> 두 블록이 연결되어 있을 가능성 있음!!!!!! -> 이거 disconnect_linked_list 구현할때 꼭꼮꼭 신경쓰렴 수빈아
    // 아니면 두 블록을 끊는 disconnetc_two_blocks를 새로 만들자!
    // bp위치 앞 블록의 bp로 이동해야함!!
    else {
        // disconnect_two_block(PREV_BLKP(bp), NEXT_BLKP(bp));
        disconnect_linked_list(PREV_BLKP(bp));
        disconnect_linked_list(NEXT_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = (PREV_BLKP(bp));
    }

    extend_linked_list(bp);
    return bp;
}

void mm_free(void *bp) {
    // 일단 지금 bp의 헤더에서 현재 블록의 사이즈 받아옴
    size_t size = GET_SIZE(HDRP(bp));

    // 현재 블록의 헤더와 푸터 할당 -> 할당 x로 바꾸어줌
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 앞 뒤 블록 가용 상태였을수도 있으니까 확인해주기
    coalesce(bp);
}

// 인자로 주어진 size 만큼의 메모리를 할당해준다.
void *mm_malloc(size_t size) {
    // 인자로 주어진 size -> 수정을 거친 진짜 할당해줄 사이즈
    size_t asize;
    // 크기 부족하면 늘려야하는 사이즈
    size_t extend_size;
    char *bp;

    // 가짜 요청 컷
    if (size == 0){
        return NULL;
    }

    // asize 계산 과정
    // 더블 워드에서 최소 바이트 -> 16
    // 최소 바이트 크기 할당해주는 경우
    if (size <= DSIZE){
        // 그냥 16바이트
        asize = 2*DSIZE;
    }
    // 8 바이트 초과 -> 8의 배수로 계산해주긔
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // asize 만큼 가용 리스트 있는지 탐색 ㄱㄱ
    // 공간 있으면 새로 할당한 bp 리턴하고 끝
    if ((bp = find_fit(asize)) != NULL) {
        // 블록 배치 => 내가 구현해야함
        place(bp, asize);
        return bp;
    }

    // 공간 없으면
    extend_size = MAX(asize, CHUNKSIZE);
    // 힙 새로 확장 (extend_size / WSIZE)는 word 개수임)
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL){
        return NULL;
    }
    // 블록 배치
    place(bp, asize);
    // 새로 할당한 bp 리턴
    return bp;
}

// malloc으로 할당 받았던 힙 영역 size 변경해서 재할당 받기!!!
void *mm_realloc(void *ptr, size_t size)
{
    // 기존의 포인터 -> 기존에 할당 받은 메모리 시작 주소
    void *oldptr = ptr;
    // 새로운 포인터 -> 새로 할당 받은 메모리 시작 주소
    void *newptr;
    // 기존의 포인터에서 복사할 크기 저장할 변수
    size_t copySize;

    // 일단 원하는 size만큼 새로 할당 받음
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    // 기존에 할당 받은 크기 받아오기
    copySize = GET_SIZE(HDRP(oldptr));

    // 둘 중 더 작은 게 copysize가 된다.
    // 새로 할당 받고 싶은게 더 작다면 -> 괜히 더 많이 복사하면 시간 낭비임
    // 원래 사이즈가 더 작으면 -> 그냥 원래 있던 데이터 다 복사하면 되니까
    if (size < copySize)
      copySize = size;
    // 기존 블록의 copysize만큼의 데이터를 newptr로 복사한다
    memcpy(newptr, oldptr, copySize);
    // 기존 블록 해제하기
    mm_free(oldptr);
    return newptr;
}

// first fit으로 뒤지기
// 찾으면 그 블록의 포인터 리턴해줘야함
static void *find_fit(size_t asize){
    void *bp = root;
    // 가용 블록 리스트 처음부터 끝까지 뒤지기 -> first fit
    while (bp != NULL) {
        if (GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
        bp = NEXT_FREEP(bp);
    }
    return NULL;
}

// find_fit이 뱉어낸 bp 위치에 asize만큼 배치해주는 함수
static void place(void *bp, size_t asize) {
    // 현재 가용 블록의 전체 크기
    size_t csize = GET_SIZE(HDRP(bp));
    disconnect_linked_list(bp);
    // csize랑 asize 차이가 16바이트 (4워드) 보다 작으면 사용 가능!
    // 왜냐면 할당해주고 남은 애들 다시
    // 패딩 
    if((csize - asize) >= (2 * DSIZE)) {
        // 필요한 부분 만큼 사용했다고 표시해주고
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 남은 부분도 표시 업데이트 해준다
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        extend_linked_list(bp);
    }
    // 분할 안 하고 그냥 다 쓰겠다
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}