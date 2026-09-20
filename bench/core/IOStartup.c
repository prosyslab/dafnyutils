#define _GNU_SOURCE
#include "IOStartup.h"

#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/magic.h>
#include <pthread.h>
#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/vfs.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__) || !defined(__GLIBC__)
#error "startup runtime supports Linux x86_64 glibc"
#endif
#ifndef DFY_STARTUP_COMPILE_PROFILE
#define DFY_STARTUP_COMPILE_PROFILE DFY_STARTUP_MANAGED_TRANSFER
#endif
#if DFY_STARTUP_COMPILE_PROFILE != DFY_STARTUP_MANAGED_TRANSFER && \
    DFY_STARTUP_COMPILE_PROFILE != DFY_STARTUP_NATIVE_REFERENCE
#error "invalid startup compile profile"
#endif
_Static_assert(sizeof(rlim_t) == 8 && sizeof(off_t) == 8, "unexpected Linux ABI");
_Static_assert(RLIM_NLIMITS == 16 && RLIMIT_NOFILE == 7 && RLIMIT_AS == 9 &&
               RLIMIT_RTTIME == 15, "unexpected Linux resource ids");

struct standard_capability {
  uint32_t source_state;
  int fd;
  int flags;
  int availability_errno;
  int stat_errno;
  struct stat status;
  bool taken;
};

static struct standard_capability standards[3];
static struct sigaction original_pipe_action;
static bool original_pipe_blocked;
static bool original_pipe_pending;
static uint8_t snapshot_bytes[DFY_STARTUP_SNAPSHOT_BYTES];
static int observer_fd = -1;
static uint64_t launch_id;
static bool bootstrapped;
static bool utility_entered;
static pthread_mutex_t state_lock = PTHREAD_MUTEX_INITIALIZER;

static uint32_t get32(const uint8_t *p) {
  return (uint32_t)p[0] | (uint32_t)p[1] << 8 |
         (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}

static uint64_t get64(const uint8_t *p) {
  return (uint64_t)get32(p) | (uint64_t)get32(p + 4) << 32;
}

static void put32(uint8_t *p, uint32_t value) {
  for (unsigned i = 0; i < 4; ++i) p[i] = (uint8_t)(value >> (8 * i));
}

static void put64(uint8_t *p, uint64_t value) {
  for (unsigned i = 0; i < 8; ++i) p[i] = (uint8_t)(value >> (8 * i));
}

/* Private framing transport only: it must not generate a utility SIGPIPE. */
static int send_event(uint32_t kind, const uint8_t *payload, uint32_t size) {
  uint8_t record[DFY_STARTUP_EVENT_HEADER_BYTES + DFY_STARTUP_SNAPSHOT_BYTES] = {0};
  memcpy(record, DFY_STARTUP_EVENT_MAGIC, 8);
  put32(record + 8, DFY_STARTUP_VERSION);
  put32(record + 12, kind);
  put32(record + 16, size);
  put64(record + 24, launch_id);
  memcpy(record + DFY_STARTUP_EVENT_HEADER_BYTES, payload, size);
  size_t sent = 0;
  size_t total = DFY_STARTUP_EVENT_HEADER_BYTES + size;
  while (sent < total) {
    ssize_t count = send(observer_fd, record + sent, total - sent, MSG_NOSIGNAL);
    if (count < 0) {
      if (errno == EINTR) continue;
      return errno;
    }
    sent += (size_t)count;
  }
  return 0;
}

static int send_error(uint32_t event, uint32_t phase, uint32_t kind, uint32_t code) {
  uint8_t payload[DFY_STARTUP_ERROR_BYTES] = {0};
  put32(payload, phase);
  put32(payload + 4, kind);
  put32(payload + 8, code);
  return send_event(event, payload, sizeof(payload));
}

static _Noreturn void fail(uint32_t phase, uint32_t kind, uint32_t code) {
  if (observer_fd >= 0)
    (void)send_error(DFY_EVENT_BOOTSTRAP_ERROR, phase, kind, code);
  _exit(DFY_STARTUP_FAILURE_EXIT);
}

static _Noreturn void system_failure(uint32_t phase, int code) {
  fail(phase, DFY_FAILURE_SYSTEM, (uint32_t)code);
}

static _Noreturn void configuration_failure(uint32_t phase, uint32_t code) {
  fail(phase, DFY_FAILURE_CONFIGURATION, code);
}

static void read_exact(int fd, uint8_t *bytes, size_t size) {
  size_t consumed = 0;
  while (consumed < size) {
    ssize_t count = read(fd, bytes + consumed, size - consumed);
    if (count < 0) {
      if (errno == EINTR) continue;
      system_failure(DFY_PHASE_CONTROL, errno);
    }
    if (count == 0) configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_TRUNCATED);
    consumed += (size_t)count;
  }
}

static int parse_control_fd(void) {
  const char *value = getenv(DFY_STARTUP_CONTROL_ENV);
  if (!value) configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_MISSING_CONTROL);
  if (!*value) configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_INVALID_CONTROL_FD);
  uint32_t fd = 0;
  for (const unsigned char *p = (const unsigned char *)value; *p; ++p) {
    if (*p < '0' || *p > '9' || fd > ((uint32_t)INT_MAX - (*p - '0')) / 10)
      configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_INVALID_CONTROL_FD);
    fd = fd * 10 + (*p - '0');
  }
  if (fd < 3) configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_INVALID_CONTROL_FD);
  return (int)fd;
}

static int descriptor_flags(int fd, uint32_t phase) {
  int flags = fcntl(fd, F_GETFL);
  if (flags < 0) system_failure(phase, errno);
  return flags;
}

static uint32_t pipe_disposition(const struct sigaction *action) {
  if (action->sa_handler == SIG_DFL) return 0;
  if (action->sa_handler == SIG_IGN) return 1;
  return 2;
}

static void validate_pipe(int fd, int access_mode) {
  int flags = descriptor_flags(fd, DFY_PHASE_CONTROL);
  if ((flags & O_ACCMODE) != access_mode)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  struct stat status;
  struct statfs filesystem;
  if (fstat(fd, &status) < 0 || fstatfs(fd, &filesystem) < 0)
    system_failure(DFY_PHASE_CONTROL, errno);
  if (!S_ISFIFO(status.st_mode) || filesystem.f_type != PIPEFS_MAGIC)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
}

static void make_cloexec(int fd, uint32_t phase) {
  int flags = fcntl(fd, F_GETFD);
  if (flags < 0 || fcntl(fd, F_SETFD, flags | FD_CLOEXEC) < 0)
    system_failure(phase, errno);
}

static void capture_standards(const uint8_t *early) {
  for (int role = 0; role < 3; ++role) {
    struct standard_capability *cap = &standards[role];
    const uint8_t *record = early + 24 + role * 12;
    cap->source_state = get32(record);
    cap->fd = (int32_t)get32(record + 4);
    cap->availability_errno = (int)get32(record + 8);
    if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER &&
        cap->source_state != DFY_SOURCE_INHERITED) {
      cap->fd = -1;
      cap->flags = 0;
      cap->stat_errno = EBADF;
    } else if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER) {
      /* An advertised live slot failing lookup is infrastructure failure. */
      cap->flags = descriptor_flags(cap->fd, DFY_PHASE_CAPTURE);
      make_cloexec(cap->fd, DFY_PHASE_TRANSFER);
      if (fstat(cap->fd, &cap->status) < 0) cap->stat_errno = errno;
    } else {
      cap->fd = role;
      cap->flags = fcntl(role, F_GETFL);
      if (cap->flags < 0) {
        if (errno != EBADF) system_failure(DFY_PHASE_CAPTURE, errno);
        cap->fd = -1;
        cap->flags = 0;
        cap->availability_errno = EBADF;
        cap->stat_errno = EBADF;
      } else {
        cap->availability_errno = 0;
        if (fstat(role, &cap->status) < 0) cap->stat_errno = errno;
      }
    }
  }
  if (sigaction(SIGPIPE, NULL, &original_pipe_action) < 0)
    system_failure(DFY_PHASE_CAPTURE, errno);
  if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER &&
      original_pipe_action.sa_handler != SIG_DFL &&
      original_pipe_action.sa_handler != SIG_IGN)
    configuration_failure(DFY_PHASE_CAPTURE, DFY_CONFIG_FIELDS);
  sigset_t mask;
  int error = pthread_sigmask(SIG_SETMASK, NULL, &mask);
  if (error) system_failure(DFY_PHASE_CAPTURE, error);
  original_pipe_blocked = sigismember(&mask, SIGPIPE) == 1;
  if (sigpending(&mask) < 0) system_failure(DFY_PHASE_CAPTURE, errno);
  original_pipe_pending = sigismember(&mask, SIGPIPE) == 1;
  put32(snapshot_bytes, DFY_STARTUP_VERSION);
  put32(snapshot_bytes + 4, (uint32_t)getpid());
  put32(snapshot_bytes + 8, pipe_disposition(&original_pipe_action));
  put32(snapshot_bytes + 12, original_pipe_blocked);
  put32(snapshot_bytes + 16, 3);
  put32(snapshot_bytes + 20, 16);
  put32(snapshot_bytes + 24, (uint32_t)syscall(SYS_gettid));
  put32(snapshot_bytes + 28, original_pipe_pending);
  for (int resource = 0; resource < 16; ++resource) {
    uint8_t *record = snapshot_bytes + DFY_STARTUP_RESOURCE_OFFSET +
                      resource * DFY_STARTUP_RESOURCE_BYTES;
    struct rlimit limit;
    put32(record, (uint32_t)resource);
    if (getrlimit(resource, &limit) < 0) {
      put32(record + 4, (uint32_t)errno);
      continue;
    }
    put64(record + 8, limit.rlim_cur == RLIM_INFINITY ? 0 : limit.rlim_cur);
    put64(record + 16, limit.rlim_max == RLIM_INFINITY ? 0 : limit.rlim_max);
    put32(record + 24, (limit.rlim_cur == RLIM_INFINITY ? 1u : 0u) |
                       (limit.rlim_max == RLIM_INFINITY ? 2u : 0u));
  }
}

static void serialize_standard(unsigned role) {
  const struct standard_capability *cap = &standards[role];
  uint8_t *record = snapshot_bytes + DFY_STARTUP_STANDARD_OFFSET +
                    role * DFY_STARTUP_STANDARD_BYTES;
  put32(record, role);
  put32(record + 4, cap->availability_errno == 0);
  put32(record + 8, (uint32_t)cap->fd);
  put32(record + 12, (uint32_t)cap->flags);
  put32(record + 16, (uint32_t)cap->availability_errno);
  put32(record + 20, (uint32_t)cap->stat_errno);
  put32(record + 24, cap->stat_errno == 0);
  put32(record + 28, cap->source_state);
  put32(record + 100, DFY_STARTUP_COMPILE_PROFILE);
  if (cap->stat_errno) return;
  const struct stat *st = &cap->status;
  put64(record + 32, st->st_dev);
  put64(record + 40, st->st_ino);
  put64(record + 48, st->st_rdev);
  put64(record + 56, (uint64_t)st->st_size);
  put64(record + 64, (uint64_t)st->st_blocks);
  put64(record + 72, (uint64_t)st->st_blksize);
  put64(record + 80, st->st_nlink);
  put32(record + 88, st->st_mode);
  put32(record + 92, st->st_uid);
  put32(record + 96, st->st_gid);
  put64(record + 104, (uint64_t)st->st_atim.tv_sec);
  put64(record + 112, (uint64_t)st->st_atim.tv_nsec);
  put64(record + 120, (uint64_t)st->st_mtim.tv_sec);
  put64(record + 128, (uint64_t)st->st_mtim.tv_nsec);
  put64(record + 136, (uint64_t)st->st_ctim.tv_sec);
  put64(record + 144, (uint64_t)st->st_ctim.tv_nsec);
}

static void validate_early_record(const uint8_t *early, const int *transport_fds,
                                  size_t transport_count) {
  if (memcmp(early, DFY_STARTUP_EARLY_MAGIC, 8))
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_MAGIC);
  if (get32(early + 8) != DFY_STARTUP_VERSION)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_VERSION);
  if (get32(early + 12) != DFY_STARTUP_EARLY_BYTES)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_LENGTH);
  if (get64(early + 16) != launch_id ||
      get32(early + 60) != DFY_STARTUP_COMPILE_PROFILE)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  for (unsigned role = 0; role < 3; ++role) {
    const uint8_t *record = early + 24 + role * 12;
    uint32_t source = get32(record);
    int fd = (int32_t)get32(record + 4);
    uint32_t unavailable = get32(record + 8);
    if (source == DFY_SOURCE_INHERITED) {
      if (unavailable ||
          (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER && fd < 3) ||
          (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE &&
           fd != (int)role))
        configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
      if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER) {
        for (size_t i = 0; i < transport_count; ++i)
          if (fd == transport_fds[i])
            configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
        for (unsigned previous = 0; previous < role; ++previous)
          if (fd == (int32_t)get32(early + 28 + previous * 12))
            configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
      }
    } else if ((source != DFY_SOURCE_CLOSED && source != DFY_SOURCE_EXEC_CLOSED) ||
               fd != -1 || unavailable != EBADF) {
      configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
    }
  }
}

static void require_eof(int fd) {
  uint8_t extra;
  ssize_t count;
  do { count = read(fd, &extra, 1); } while (count < 0 && errno == EINTR);
  if (count < 0) system_failure(DFY_PHASE_CONTROL, errno);
  if (count) configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_EXTRA_DATA);
}

static void restore_environment(const char *key, bool present,
                                const uint8_t *bytes, uint32_t length) {
  if (!present) {
    if (unsetenv(key) < 0) system_failure(DFY_PHASE_ENVIRONMENT, errno);
    return;
  }
  char *value = malloc((size_t)length + 1);
  if (!value) system_failure(DFY_PHASE_ENVIRONMENT, errno);
  memcpy(value, bytes, length);
  value[length] = '\0';
  if (setenv(key, value, 1) < 0) system_failure(DFY_PHASE_ENVIRONMENT, errno);
  free(value);
}

static void initialize(void) {
  int control = parse_control_fd();
  validate_pipe(control, O_RDONLY);
  uint8_t header[DFY_STARTUP_CONTROL_BYTES];
  read_exact(control, header, sizeof(header));
  if (memcmp(header, DFY_STARTUP_CONTROL_MAGIC, 8))
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_MAGIC);
  if (get32(header + 8) != DFY_STARTUP_VERSION)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_VERSION);
  uint32_t preload_length = get32(header + 36);
  uint32_t original_length = get32(header + 44);
  uint64_t total = (uint64_t)DFY_STARTUP_CONTROL_BYTES + preload_length + original_length;
  if (get32(header + 12) != DFY_STARTUP_CONTROL_BYTES || total > UINT32_MAX ||
      get32(header + 16) != total)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_LENGTH);
  int runtime_stdout = (int32_t)get32(header + 20);
  int runtime_stderr = (int32_t)get32(header + 24);
  int observer = (int32_t)get32(header + 28);
  int early_fd = (int32_t)get32(header + 64);
  uint32_t profile = get32(header + 48);
  if (runtime_stdout < 3 || runtime_stderr < 3 || observer < 3 || early_fd < 3 ||
      early_fd == control || early_fd == runtime_stdout ||
      early_fd == runtime_stderr || early_fd == observer || get32(header + 68) ||
      runtime_stdout == runtime_stderr || runtime_stdout == observer ||
      runtime_stderr == observer || control == runtime_stdout ||
      control == runtime_stderr || control == observer ||
      get32(header + 32) > 1 || get32(header + 40) > 1 ||
      (!get32(header + 32) && preload_length) ||
      (!get32(header + 40) && original_length) ||
      profile > DFY_STARTUP_NATIVE_REFERENCE || get32(header + 52))
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  validate_pipe(runtime_stdout, O_WRONLY);
  validate_pipe(runtime_stderr, O_WRONLY);
  validate_pipe(early_fd, O_RDONLY);
  int socket_type;
  socklen_t socket_type_size = sizeof(socket_type);
  if (getsockopt(observer, SOL_SOCKET, SO_TYPE, &socket_type, &socket_type_size) < 0)
    system_failure(DFY_PHASE_CONTROL, errno);
  if (socket_type != SOCK_STREAM)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  observer_fd = observer;
  launch_id = get64(header + 56);
  if (profile != DFY_STARTUP_COMPILE_PROFILE)
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  make_cloexec(observer_fd, DFY_PHASE_CONTROL);
  size_t payload_length = (size_t)(total - DFY_STARTUP_CONTROL_BYTES);
  uint8_t *payload = malloc(payload_length ? payload_length : 1);
  if (!payload) system_failure(DFY_PHASE_CONTROL, errno);
  read_exact(control, payload, payload_length);
  if (memchr(payload, 0, payload_length))
    configuration_failure(DFY_PHASE_CONTROL, DFY_CONFIG_FIELDS);
  require_eof(control);
  uint8_t early[DFY_STARTUP_EARLY_BYTES];
  read_exact(early_fd, early, sizeof(early));
  require_eof(early_fd);
  const int transport_fds[] = {control, early_fd, runtime_stdout, runtime_stderr, observer};
  validate_early_record(early, transport_fds, sizeof(transport_fds) / sizeof(transport_fds[0]));
  capture_standards(early);
  for (unsigned role = 0; role < 3; ++role) serialize_standard(role);
  if (close(control) < 0 || close(early_fd) < 0 || close(runtime_stdout) < 0 ||
      close(runtime_stderr) < 0) system_failure(DFY_PHASE_TRANSFER, errno);
  restore_environment("LD_PRELOAD", get32(header + 32), payload, preload_length);
  restore_environment(DFY_STARTUP_CONTROL_ENV, get32(header + 40),
                      payload + preload_length, original_length);
  free(payload);
  int error = send_event(DFY_EVENT_BOOTSTRAP_READY, snapshot_bytes, sizeof(snapshot_bytes));
  if (error) system_failure(DFY_PHASE_TRANSPORT, error);
  bootstrapped = true;
}

int32_t dfy_startup_snapshot(uint8_t *bytes, uint32_t capacity, uint32_t *required_bytes) {
  if (!bytes || !required_bytes) return DFY_STARTUP_INVALID_ARGUMENT;
  *required_bytes = 0;
  pthread_mutex_lock(&state_lock);
  int32_t result = DFY_STARTUP_NOT_BOOTSTRAPPED;
  if (bootstrapped) {
    *required_bytes = DFY_STARTUP_SNAPSHOT_BYTES;
    result = capacity < DFY_STARTUP_SNAPSHOT_BYTES ? DFY_STARTUP_BUFFER_TOO_SMALL : DFY_STARTUP_OK;
    if (result == DFY_STARTUP_OK) memcpy(bytes, snapshot_bytes, DFY_STARTUP_SNAPSHOT_BYTES);
  }
  pthread_mutex_unlock(&state_lock);
  return result;
}

int32_t dfy_startup_take_standard(uint32_t role, int32_t *native_fd,
                                 uint32_t *availability_errno) {
  if (!native_fd || !availability_errno) return DFY_STARTUP_INVALID_ARGUMENT;
  *native_fd = -1;
  *availability_errno = 0;
  if (role > 2) return DFY_STARTUP_INVALID_ARGUMENT;
  pthread_mutex_lock(&state_lock);
  int32_t result = DFY_STARTUP_NOT_BOOTSTRAPPED;
  if (bootstrapped) {
    if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE)
      result = DFY_STARTUP_PROFILE_FORBIDS_TAKE;
    else if (standards[role].taken) result = DFY_STARTUP_ALREADY_TAKEN;
    else {
      standards[role].taken = true;
      *native_fd = standards[role].fd;
      *availability_errno = (uint32_t)standards[role].availability_errno;
      result = DFY_STARTUP_OK;
    }
  }
  pthread_mutex_unlock(&state_lock);
  return result;
}

static int restore_pipe(void) {
  if (sigaction(SIGPIPE, &original_pipe_action, NULL) < 0) return errno;
  sigset_t mask;
  int error = pthread_sigmask(SIG_SETMASK, NULL, &mask);
  if (error) return error;
  if (original_pipe_blocked) sigaddset(&mask, SIGPIPE);
  else sigdelset(&mask, SIGPIPE);
  error = pthread_sigmask(SIG_SETMASK, &mask, NULL);
  if (error) return error;
  if (original_pipe_pending && original_pipe_blocked) {
    if (sigpending(&mask) < 0) return errno;
    if (sigismember(&mask, SIGPIPE) != 1) return pthread_kill(pthread_self(), SIGPIPE);
  }
  return 0;
}

int32_t dfy_startup_enter_utility(uint32_t *failure_kind, uint32_t *failure_code) {
  int entry_errno = errno;
  if (!failure_kind || !failure_code) return DFY_STARTUP_INVALID_ARGUMENT;
  *failure_kind = 0;
  *failure_code = 0;
  pthread_mutex_lock(&state_lock);
  int32_t result;
  if (!bootstrapped) result = DFY_STARTUP_NOT_BOOTSTRAPPED;
  else if (utility_entered) result = DFY_STARTUP_ALREADY_ENTERED;
  else if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER &&
           (!standards[0].taken || !standards[1].taken || !standards[2].taken))
    result = DFY_STARTUP_NOT_READY;
  else {
    int error = DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_MANAGED_TRANSFER
                    ? restore_pipe() : 0;
    if (error) {
      *failure_kind = DFY_FAILURE_SYSTEM;
      *failure_code = (uint32_t)error;
      (void)send_error(DFY_EVENT_UTILITY_ENTRY_ERROR, DFY_PHASE_UTILITY,
                       *failure_kind, *failure_code);
      result = DFY_STARTUP_NATIVE_FAILURE;
    } else {
      uint8_t payload[DFY_STARTUP_REFERENCE_ENTRY_BYTES] = {0};
      struct sigaction current_pipe_action;
      sigset_t current_mask;
      if (sigaction(SIGPIPE, NULL, &current_pipe_action) < 0) error = errno;
      else {
        error = pthread_sigmask(SIG_SETMASK, NULL, &current_mask);
      }
      if (error) {
        *failure_kind = DFY_FAILURE_SYSTEM;
        *failure_code = (uint32_t)error;
        (void)send_error(DFY_EVENT_UTILITY_ENTRY_ERROR, DFY_PHASE_UTILITY,
                         *failure_kind, *failure_code);
        pthread_mutex_unlock(&state_lock);
        if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE)
          errno = entry_errno;
        return DFY_STARTUP_NATIVE_FAILURE;
      }
      put32(payload, (uint32_t)getpid());
      put32(payload + 4, (uint32_t)syscall(SYS_gettid));
      put32(payload + 8, pipe_disposition(&current_pipe_action));
      put32(payload + 12, sigismember(&current_mask, SIGPIPE) == 1);
      uint32_t entry_bytes = DFY_STARTUP_ENTRY_BYTES;
      if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE) {
        entry_bytes = DFY_STARTUP_REFERENCE_ENTRY_BYTES;
        for (int role = 0; role < 3; ++role) {
          int flags = fcntl(role, F_GETFD);
          uint8_t *record = payload + 16 + role * 8;
          if (flags < 0) {
            if (errno != EBADF) {
              *failure_kind = DFY_FAILURE_SYSTEM;
              *failure_code = (uint32_t)errno;
              (void)send_error(DFY_EVENT_UTILITY_ENTRY_ERROR, DFY_PHASE_UTILITY,
                               *failure_kind, *failure_code);
              pthread_mutex_unlock(&state_lock);
              errno = entry_errno;
              return DFY_STARTUP_NATIVE_FAILURE;
            }
            put32(record + 4, EBADF);
          } else {
            put32(record, 1);
          }
        }
      }
      error = send_event(DFY_EVENT_UTILITY_ENTERED, payload, entry_bytes);
      if (error) {
        *failure_kind = DFY_FAILURE_SYSTEM;
        *failure_code = (uint32_t)error;
        result = DFY_STARTUP_TRANSPORT_FAILURE;
      } else {
        utility_entered = true;
        result = DFY_STARTUP_OK;
      }
    }
  }
  pthread_mutex_unlock(&state_lock);
  if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE)
    errno = entry_errno;
  return result;
}

typedef int (*native_main)(int, char **, char **);
typedef int (*libc_start_main)(native_main, int, char **, void (*)(void),
                               void (*)(void), void (*)(void), void *);

static native_main reference_main;

static int reference_main_entry(int argc, char **argv, char **envp) {
  int saved_errno = errno;
  uint32_t failure_kind;
  uint32_t failure_code;
  int32_t status = dfy_startup_enter_utility(&failure_kind, &failure_code);
  if (status != DFY_STARTUP_OK) _exit(DFY_STARTUP_FAILURE_EXIT);
  errno = saved_errno;
  return reference_main(argc, argv, envp);
}

DFY_STARTUP_EXPORT int __libc_start_main(native_main main, int argc, char **argv,
    void (*init)(void), void (*fini)(void), void (*rtld_fini)(void), void *stack_end) {
  int incoming_errno = errno;
  libc_start_main next = (libc_start_main)dlsym(RTLD_NEXT, "__libc_start_main");
  if (!next) configuration_failure(DFY_PHASE_LIBC_ENTRY, DFY_CONFIG_LIFECYCLE);
  initialize();
  if (DFY_STARTUP_COMPILE_PROFILE == DFY_STARTUP_NATIVE_REFERENCE) {
    reference_main = main;
    main = reference_main_entry;
    errno = incoming_errno;
  }
  return next(main, argc, argv, init, fini, rtld_fini, stack_end);
}
