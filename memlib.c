/*
 * memlib.c - a module that simulates the memory system.  Needed because it 
 *            allows us to interleave calls from the student's malloc package 
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk;  /* points to first byte of heap */
static char *mem_brk;        /* points to last byte of heap */
static char *mem_max_addr;   /* largest legal heap address */ 

/* 
 * mem_init - initialize the memory system model
 */
void mem_init(void)
{
    // config.h 참고 #define MAX_HEAP (20*(1<<20)) : 20971520bytes == 20 MB
    // 20MB 만큼의 MAX_HEAP을 동적할당 먼저 해온다
    // 그 때의 시작점 : mem_start_brk
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL) {
	fprintf(stderr, "mem_init_vm: malloc error\n");
	exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP;
    // 아무것도 할당되지 않은 상태이기 때문에 mem_start_brk == mem_brk
    mem_brk = mem_start_brk;            
}

/* 
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 */
// 바이트 형태로 입력 받기
// 초기화 성공하면 0 아니면 -1
void *mem_sbrk(int incr) 
{
    // 힙 늘어나기 전 끝 부분
    char *old_brk = mem_brk;

    if ( (incr < 0) || ((mem_brk + incr) > mem_max_addr)) {
	errno = ENOMEM;
	fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
	// 리턴 값이 void* 임
    return (void *)-1;
    }

    mem_brk += incr;
    return (void *)old_brk;
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/* 
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize() 
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
