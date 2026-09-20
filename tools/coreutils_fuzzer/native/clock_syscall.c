#define _GNU_SOURCE

#include <time.h>
#include <sys/syscall.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error "clock observer supports only Linux x86_64"
#endif

#if !defined(SYS_clock_gettime) || SYS_clock_gettime != 228
#error "unexpected Linux x86_64 clock_gettime syscall number"
#endif

_Static_assert(sizeof(long) == 8, "clock observer requires the x86_64 LP64 ABI");
_Static_assert(sizeof(time_t) == 8, "clock observer requires a 64-bit time_t");

__attribute__((visibility("default")))
int clock_gettime(clockid_t clock_id, struct timespec *value) {
  return (int)syscall(SYS_clock_gettime, clock_id, value);
}
