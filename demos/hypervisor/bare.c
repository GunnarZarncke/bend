// hypervisor: the bare lane's host, a freestanding aarch64 image for EL2
// with no libc and no OS. build.sh passes -DBEND_LANE='"bare.c"', and the
// runtime includes this file twice: after its types, for the shim (the
// UART, the semihosting exit, the bump heap, the string and stream
// functions the runtime calls, the memory and signal calls as it makes
// them, and the prototypes of what boot.c defines), and at its end with
// BEND_LANE_END, when this file includes boot.c (the boot, the default
// vectors, bend_main, and the event loop without descriptors).

#ifndef BEND_LANE_END
#include <stddef.h>
#include <stdarg.h>
#include <stdatomic.h>

// the runtime's names the shim's prototypes need, as the template
// declares them (C lets a typedef repeat); the bodies are at the end
struct IoWork;
typedef void (*IoCall)(struct IoWork* w);
typedef Term (*IoPack)(Env e, struct IoWork* w);
static int   f32_text(char* buf, f32 v);
static void  io_take(Env e);
static Term  io_work(struct IoWork* w, IoCall call, IoPack pack);
static void  io_wait(Env e);

// Bare
// ====

// The bare lane (-o x.elf) runs freestanding at EL2 on one ARM64 core:
// no libc, a PL011 UART for the streams, semihosting for exit, and the
// arena, the term stack and the persist region from the linker script.
// The shims below stand in for the libc the host lane includes; every
// other host function keeps its text. The heap resets per bend_main.

typedef int  FILE;
typedef long ssize_t;
#define stdout  ((FILE*)1)
#define stderr  ((FILE*)2)
#define EINTR   4
#define POLLIN  1
#define POLLOUT 4
#define MAP_FAILED ((void*)-1)
static int errno;

typedef int pthread_t;
typedef int pthread_mutex_t;
typedef int pthread_cond_t;
#define PTHREAD_MUTEX_INITIALIZER 0
#define PTHREAD_COND_INITIALIZER  0
#define pthread_mutex_lock(m)      ((void)0)
#define pthread_mutex_unlock(m)    ((void)0)
#define pthread_cond_wait(c, m)    ((void)0)
#define pthread_cond_signal(c)     ((void)0)
#define pthread_cond_broadcast(c)  ((void)0)
#define pthread_detach(t)          ((void)0)
#define pthread_create(t, a, f, x) 1

extern char __arena_start[], __arena_end[], __stack_lo[], __stack_hi[];
extern char __persist_start[], __persist_end[];

#define BARE_HEAP  (64ull << 20)
#define BARE_UART  ((volatile uint32_t*)0x09000000)
#define BEND_LANE_SPAN  ((u64)(__arena_end - __arena_start) - BARE_HEAP)

// The host's memory and signal calls, as the runtime makes them. mmap has
// two callers: pool_stack asks with no address and gets the term stack,
// the linker's region whatever the size asked; corpus_map and corpus_grow
// ask at an address and get the corpus, the arena past the heap, so
// corpus_map's search for a hint settles on it and corpus_grow, answered
// with another address than it asked, declines. munmap and mprotect do
// nothing, and the stack guard's signals are never delivered: a run off
// the term stack faults into the vectors, which report it.
#define PROT_NONE     0
#define PROT_READ     1
#define PROT_WRITE    2
#define MAP_PRIVATE   2
#define MAP_ANON      0x1000
#define MAP_NORESERVE 0x4000
#define SIGSTKSZ      16384
#define SA_ONSTACK    0
#define SIGSEGV       11
#define SIGBUS        10
#define SIGPIPE       13
#define SIG_IGN       ((void (*)(int))1)
#define F_SETFL       4
#define O_NONBLOCK    4
#define CLOCK_MONOTONIC      1
#define _SC_NPROCESSORS_ONLN 84
typedef struct { void* ss_sp; size_t ss_size; } stack_t;
struct sigaction { void (*sa_handler)(int); int sa_flags; };
struct timespec { long tv_sec; long tv_nsec; };

static inline void* mmap(void* at, size_t len, int prot, int flags, int fd, long off) {
  return at == NULL ? (void*)__stack_lo : (void*)(__arena_start + BARE_HEAP);
}

static inline int munmap(void* at, size_t len) {
  return 0;
}

static inline int mprotect(void* at, size_t len, int prot) {
  return 0;
}

static inline int sigaltstack(const stack_t* ss, stack_t* old) {
  return 0;
}

static inline int sigaction(int sig, const struct sigaction* sa, struct sigaction* old) {
  return 0;
}

static inline void (*signal(int sig, void (*h)(int)))(int) {
  return h;
}

static inline int pipe(int fds[2]) {
  fds[0] = -1;
  fds[1] = -1;
  return 0;
}

static inline int fcntl(int fd, int cmd, ...) {
  return 0;
}

// the counter, in the timer's units
static inline int clock_gettime(int clk, struct timespec* ts) {
  uint64_t c;
  uint64_t f;
  __asm__ volatile("isb\n\tmrs %0, cntpct_el0" : "=r"(c) : : "memory");
  __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(f));
  ts->tv_sec  = (long)(c / f);
  ts->tv_nsec = (long)(c % f * 1000000000ull / f);
  return 0;
}

// no files, one core, no path to the executable
static inline FILE* fopen(const char* p, const char* m) {
  return NULL;
}

static inline int fscanf(FILE* f, const char* fmt, ...) {
  return 0;
}

static inline int fclose(FILE* f) {
  return 0;
}

static inline long sysconf(int name) {
  return 1;
}

static inline ssize_t readlink(const char* p, char* buf, size_t n) {
  return 0;
}

static inline char* strcat(char* d, const char* s) {
  char* p = d;
  while (*p != 0) {
    p += 1;
  }
  while ((*p++ = *s++) != 0) {
  }
  return d;
}

static void bare_putc(char c) {
  while (BARE_UART[6] & (1u << 5)) {}
  BARE_UART[0] = (uint32_t)(unsigned char)c;
}

static void bare_puts(const char* s, uint64_t n) {
  for (uint64_t i = 0; i < n; i += 1) {
    bare_putc(s[i]);
  }
}

static uint64_t bare_semi(uint64_t op, void* arg) {
  register uint64_t x0 __asm__("x0") = op;
  register void*    x1 __asm__("x1") = arg;
  __asm__ volatile("hlt #0xf000" : "+r"(x0) : "r"(x1) : "memory");
  return x0;
}

// bare_again asks the boot for one more instance: it zeroes .bss, runs
// the init array again and calls bend_main again. A hypervisor sets it
// from an effect before its main returns.
__attribute__((used)) int bare_again;

__attribute__((used, noreturn)) void bare_exit(int code) {
  uint64_t blk[2] = { 0x20026, (uint64_t)(uint32_t)code };
  for (;;) {
    bare_semi(0x18, blk);
  }
}
#define exit(c)  bare_exit(c)
#define _exit(c) bare_exit(c)

// mem and str as plain loops: -fno-builtin keeps clang from folding them
// back into the calls it emits for struct copies, which these serve.
__attribute__((used)) void* memcpy(void* d, const void* s, size_t n) {
  char* p = d;
  const char* q = s;
  for (size_t i = 0; i < n; i += 1) {
    p[i] = q[i];
  }
  return d;
}

__attribute__((used)) void* memmove(void* d, const void* s, size_t n) {
  char* p = d;
  const char* q = s;
  if (p < q) {
    for (size_t i = 0; i < n; i += 1) {
      p[i] = q[i];
    }
  } else {
    for (size_t i = n; i > 0; i -= 1) {
      p[i - 1] = q[i - 1];
    }
  }
  return d;
}

__attribute__((used)) void* memset(void* d, int c, size_t n) {
  char* p = d;
  for (size_t i = 0; i < n; i += 1) {
    p[i] = (char)c;
  }
  return d;
}

__attribute__((used)) size_t strlen(const char* s) {
  size_t n = 0;
  while (s[n] != 0) {
    n += 1;
  }
  return n;
}

static int strcmp(const char* a, const char* b) {
  while (*a != 0 && *a == *b) {
    a += 1;
    b += 1;
  }
  return (unsigned char)*a - (unsigned char)*b;
}

static char* strchr(const char* s, int c) {
  for (;; s += 1) {
    if (*s == (char)c) {
      return (char*)s;
    }
    if (*s == 0) {
      return NULL;
    }
  }
}

static void* memchr(const void* s, int c, size_t n) {
  const char* p = s;
  for (size_t i = 0; i < n; i += 1) {
    if (p[i] == (char)c) {
      return (void*)(p + i);
    }
  }
  return NULL;
}

static char* strpbrk(const char* s, const char* set) {
  for (; *s != 0; s += 1) {
    if (strchr(set, *s) != NULL) {
      return (char*)s;
    }
  }
  return NULL;
}

static const char* strerror(int code) {
  return "error";
}

// A bump heap over the arena's head; free is a no-op, bend_main resets it.
static char* bare_brk;

static void* malloc(size_t n) {
  n = (n + 15) & ~(size_t)15;
  if (bare_brk + 16 + n > __arena_start + BARE_HEAP) {
    return NULL;
  }
  uint64_t* h = (uint64_t*)bare_brk;
  h[0]     = n;
  bare_brk += 16 + n;
  return h + 2;
}

static void* calloc(size_t k, size_t n) {
  void* p = malloc(k * n);
  if (p != NULL) {
    memset(p, 0, k * n);
  }
  return p;
}

static void* realloc(void* p, size_t n) {
  void* q = malloc(n);
  if (p != NULL && q != NULL) {
    size_t old = ((uint64_t*)p)[-2];
    memcpy(q, p, old < n ? old : n);
  }
  return q;
}

static void free(void* p) {
}

// The streams: %s %c %d %u %x %llu %llx %.*s and %%, all the runtime says.
static void bare_num(uint64_t v, unsigned base, bool neg) {
  char b[24];
  int  n = 0;
  do {
    b[n++] = "0123456789abcdef"[v % base];
    v /= base;
  } while (v != 0);
  if (neg) {
    bare_putc('-');
  }
  while (n > 0) {
    bare_putc(b[--n]);
  }
}

static void bare_fmt(const char* f, va_list ap) {
  for (; *f != 0; f += 1) {
    if (*f != '%') {
      bare_putc(*f);
      continue;
    }
    f += 1;
    int prec = -1;
    if (*f == '.' && f[1] == '*') {
      prec = va_arg(ap, int);
      f += 2;
    }
    int longs = 0;
    while (*f == 'l') {
      longs += 1;
      f += 1;
    }
    if (*f == 's') {
      const char* s = va_arg(ap, const char*);
      bare_puts(s, prec >= 0 ? (uint64_t)prec : strlen(s));
    } else if (*f == 'c') {
      bare_putc((char)va_arg(ap, int));
    } else if (*f == 'd') {
      int64_t v = longs ? va_arg(ap, int64_t) : va_arg(ap, int);
      bare_num(v < 0 ? (uint64_t)-v : (uint64_t)v, 10, v < 0);
    } else if (*f == 'u') {
      bare_num(longs ? va_arg(ap, uint64_t) : va_arg(ap, unsigned), 10, false);
    } else if (*f == 'x') {
      bare_num(longs ? va_arg(ap, uint64_t) : va_arg(ap, unsigned), 16, false);
    } else {
      bare_putc(*f);
    }
  }
}

static int printf(const char* f, ...) {
  va_list ap;
  va_start(ap, f);
  bare_fmt(f, ap);
  va_end(ap);
  return 0;
}

static int fprintf(FILE* h, const char* f, ...) {
  va_list ap;
  va_start(ap, f);
  bare_fmt(f, ap);
  va_end(ap);
  return 0;
}

static size_t fwrite(const void* p, size_t sz, size_t n, FILE* h) {
  bare_puts(p, sz * n);
  return n;
}

static int fputs(const char* s, FILE* h) {
  bare_puts(s, strlen(s));
  return 0;
}

static int putchar(int c) {
  bare_putc((char)c);
  return c;
}

static int fflush(FILE* h) {
  return 0;
}

// No libm: a float transcendental fail-stops the program.
static double bare_math1(double x) {
  fprintf(stderr, "bend: no libm on the bare lane\n");
  bare_exit(1);
}

static double bare_math2(double x, double y) {
  return bare_math1(x);
}

#define sqrt  bare_math1
#define exp   bare_math1
#define log   bare_math1
#define log2  bare_math1
#define log10 bare_math1
#define sin   bare_math1
#define cos   bare_math1
#define tan   bare_math1
#define asin  bare_math1
#define acos  bare_math1
#define atan  bare_math1
#define sinh  bare_math1
#define cosh  bare_math1
#define tanh  bare_math1
#define floor bare_math1
#define ceil  bare_math1
#define trunc bare_math1
#define fabs  bare_math1
#define atan2 bare_math2
#define pow   bare_math2
#define fmod  bare_math2

#else
#include "boot.c"
#endif
