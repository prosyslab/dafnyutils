#include "config.h"

#include <errno.h>
#include <inttypes.h>
#include <locale.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "parse-datetime.h"
#include "posixtm.h"

#define PROTOCOL_VERSION "dafnyutils-touch-time-parser-v1"
#define MAX_DATE_BYTES (128U * 1024U)
#define HEADER_BYTES 128U

static time_t supplied_now;

time_t
__wrap_rpl_time (time_t *result)
{
  if (result != NULL)
    *result = supplied_now;
  return supplied_now;
}

static bool
read_line (char *buffer, size_t capacity)
{
  if (fgets (buffer, capacity, stdin) == NULL)
    return false;
  size_t length = strlen (buffer);
  if (length == 0 || buffer[length - 1] != '\n')
    return false;
  buffer[length - 1] = '\0';
  return true;
}

static bool
parse_intmax (char const *text, intmax_t *value)
{
  char *end = NULL;
  errno = 0;
  intmax_t parsed = strtoimax (text, &end, 10);
  if (errno != 0 || end == text || *end != '\0')
    return false;
  *value = parsed;
  return true;
}

static bool
parse_size (char const *text, size_t *value)
{
  char *end = NULL;
  errno = 0;
  uintmax_t parsed = strtoumax (text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || MAX_DATE_BYTES < parsed)
    return false;
  *value = (size_t) parsed;
  return true;
}

static int
write_invalid (void)
{
  if (printf (PROTOCOL_VERSION "\ninvalid\n") < 0 || fflush (stdout) != 0)
    return 74;
  return 0;
}

static int
write_success (struct timespec result)
{
  if (printf (PROTOCOL_VERSION "\nok\n%" PRIdMAX "\n%ld\n",
              (intmax_t) result.tv_sec, result.tv_nsec) < 0
      || fflush (stdout) != 0)
    return 74;
  return 0;
}

int
main (void)
{
  char version[HEADER_BYTES];
  char operation[HEADER_BYTES];
  char seconds_text[HEADER_BYTES];
  char nanoseconds_text[HEADER_BYTES];
  char length_text[HEADER_BYTES];
  intmax_t seconds;
  intmax_t nanoseconds;
  size_t payload_length;

  if (!read_line (version, sizeof version)
      || !read_line (operation, sizeof operation)
      || !read_line (seconds_text, sizeof seconds_text)
      || !read_line (nanoseconds_text, sizeof nanoseconds_text)
      || !read_line (length_text, sizeof length_text)
      || strcmp (version, PROTOCOL_VERSION) != 0
      || !parse_intmax (seconds_text, &seconds)
      || !parse_intmax (nanoseconds_text, &nanoseconds)
      || nanoseconds < 0 || 999999999 < nanoseconds
      || !parse_size (length_text, &payload_length))
    return 64;

  time_t reference_seconds = (time_t) seconds;
  if ((intmax_t) reference_seconds != seconds)
    return write_invalid ();

  char *payload = malloc (payload_length + 1);
  if (payload == NULL)
    return 71;
  if (fread (payload, 1, payload_length, stdin) != payload_length
      || fgetc (stdin) != EOF || ferror (stdin))
    {
      free (payload);
      return 64;
    }
  payload[payload_length] = '\0';
  if (memchr (payload, '\0', payload_length) != NULL)
    {
      free (payload);
      return write_invalid ();
    }

  if (setlocale (LC_ALL, "C") == NULL || setenv ("TZ", "UTC0", 1) != 0)
    {
      free (payload);
      return 71;
    }
  tzset ();
  supplied_now = reference_seconds;

  struct timespec result = { 0, 0 };
  bool parsed;
  if (strcmp (operation, "date") == 0)
    {
      struct timespec reference = { reference_seconds, (long) nanoseconds };
      parsed = parse_datetime (&result, payload, &reference);
    }
  else if (strcmp (operation, "timestamp") == 0)
    {
      time_t timestamp;
      parsed = posixtime (&timestamp, payload,
                          PDS_LEADING_YEAR | PDS_CENTURY | PDS_SECONDS);
      if (parsed)
        result = (struct timespec) { timestamp, 0 };
    }
  else
    {
      free (payload);
      return 64;
    }

  free (payload);
  return parsed ? write_success (result) : write_invalid ();
}
