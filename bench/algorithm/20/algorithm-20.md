# Algorithm Problem 20

- source: https://codeforces.com/problemset/problem/816/A
- difficulty: interview

## Problem Statement

Karen is getting ready for a new school day!

 [Image] 

It is currently hh:mm, given in a 24-hour format. As you know, Karen loves palindromes, and she believes that it is good luck to wake up when the time is a palindrome.

What is the minimum number of minutes she should sleep, such that, when she wakes up, the time is a palindrome?

Remember that a palindrome is a string that reads the same forwards and backwards. For instance, 05:39 is not a palindrome, because 05:39 backwards is 93:50. On the other hand, 05:50 is a palindrome, because 05:50 backwards is 05:50.


-----Input-----

The first and only line of input contains a single string in the format hh:mm (00 ≤  hh  ≤ 23, 00 ≤  mm  ≤ 59).


-----Output-----

Output a single integer on a line by itself, the minimum number of minutes she should sleep, such that, when she wakes up, the time is a palindrome.


-----Examples-----
Input
05:39

Output
11

Input
13:31

Output
0

Input
23:59

Output
1



-----Note-----

In the first test case, the minimum number of minutes Karen should sleep for is 11. She can wake up at 05:50, when the time is a palindrome.

In the second test case, Karen can wake up immediately, as the current time, 13:31, is already a palindrome.

In the third test case, the minimum number of minutes Karen should sleep for is 1 minute. She can wake up at 00:00, when the time is a palindrome.
## Apps Parser

The evaluator uses the following parser to convert each raw stdin/stdout positive test case into typed arguments. The implementation test compares `Solve(...)` return values against the output values returned by this parser.

```python
def parser(input: str, output: str) -> tuple[str, int]:
    import re

    time = ""
    s_in = input or ""
    for line in s_in.splitlines():
        m = re.fullmatch("\\s*(\\d{2}):(\\d{2})\\s*", line)
        if m:
            time = f"{m.group(1)}:{m.group(2)}"
            break
    if not time:
        m = re.search("(\\d{2}):(\\d{2})", s_in)
        if m:
            time = f"{m.group(1)}:{m.group(2)}"
        else:
            m = re.search("(\\d{1,2}):(\\d{1,2})", s_in)
            if m:
                hh = int(m.group(1))
                mm = int(m.group(2))
                time = f"{hh:02d}:{mm:02d}"
            else:
                time = ""
                for line in s_in.splitlines():
                    s = line.strip()
                    if s:
                        time = s
                        break
                time = time or s_in.strip()
    s_out = output or ""
    result: int | None = None
    for line in s_out.splitlines():
        t = line.strip()
        if t.isdigit():
            result = int(t)
            break
    if result is None:
        m = re.search("\\d+", s_out)
        if m:
            result = int(m.group(0))
        else:
            result = 0
    return (time, result)
```
