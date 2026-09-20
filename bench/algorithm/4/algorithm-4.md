# Algorithm Problem 4

- source: https://codeforces.com/problemset/problem/916/A
- difficulty: interview

## Problem Statement

Jamie loves sleeping. One day, he decides that he needs to wake up at exactly hh: mm. However, he hates waking up, so he wants to make waking up less painful by setting the alarm at a lucky time. He will then press the snooze button every x minutes until hh: mm is reached, and only then he will wake up. He wants to know what is the smallest number of times he needs to press the snooze button.

A time is considered lucky if it contains a digit '7'. For example, 13: 07 and 17: 27 are lucky, while 00: 48 and 21: 34 are not lucky.

Note that it is not necessary that the time set for the alarm and the wake-up time are on the same day. It is guaranteed that there is a lucky time Jamie can set so that he can wake at hh: mm.

Formally, find the smallest possible non-negative integer y such that the time representation of the time x·y minutes before hh: mm contains the digit '7'.

Jamie uses 24-hours clock, so after 23: 59 comes 00: 00.


-----Input-----

The first line contains a single integer x (1 ≤ x ≤ 60).

The second line contains two two-digit integers, hh and mm (00 ≤ hh ≤ 23, 00 ≤ mm ≤ 59).


-----Output-----

Print the minimum number of times he needs to press the button.


-----Examples-----
Input
3
11 23

Output
2

Input
5
01 07

Output
0



-----Note-----

In the first sample, Jamie needs to wake up at 11:23. So, he can set his alarm at 11:17. He would press the snooze button when the alarm rings at 11:17 and at 11:20.

In the second sample, Jamie can set his alarm at exactly at 01:07 which is lucky.
## Apps Parser

The evaluator uses the following parser to convert each raw stdin/stdout positive test case into typed arguments. The implementation test compares `Solve(...)` return values against the output values returned by this parser.

```python
def parser(input: str, output: str) -> tuple[int, int, int, int]:
    """
    Parses the problem input and output into (x, hh, mm, y).
    """
    s = input.strip()
    if not s:
        raise ValueError("Empty input")
    lines = [line.strip() for line in s.splitlines() if line.strip() != ""]
    first = lines[0].split()
    x = int(first[0])
    if len(lines) >= 2:
        parts = lines[1].split()
    else:
        parts = first[1:]
    if len(parts) < 2:
        raise ValueError("Could not parse hh and mm")
    hh = int(parts[0])
    mm = int(parts[1])
    out_tokens = output.strip().split()
    if not out_tokens:
        raise ValueError("Empty output")
    y = int(out_tokens[0])
    return (x, hh, mm, y)
```
