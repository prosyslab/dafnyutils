# Algorithm Problem 59

- source: https://codeforces.com/problemset/problem/920/C
- difficulty: interview

## Problem Statement

You have an array a consisting of n integers. Each integer from 1 to n appears exactly once in this array.

For some indices i (1 ≤ i ≤ n - 1) it is possible to swap i-th element with (i + 1)-th, for other indices it is not possible. You may perform any number of swapping operations any order. There is no limit on the number of times you swap i-th element with (i + 1)-th (if the position is not forbidden).

Can you make this array sorted in ascending order performing some sequence of swapping operations?


-----Input-----

The first line contains one integer n (2 ≤ n ≤ 200000) — the number of elements in the array.

The second line contains n integers a_1, a_2, ..., a_{n} (1 ≤ a_{i} ≤ 200000) — the elements of the array. Each integer from 1 to n appears exactly once.

The third line contains a string of n - 1 characters, each character is either 0 or 1. If i-th character is 1, then you can swap i-th element with (i + 1)-th any number of times, otherwise it is forbidden to swap i-th element with (i + 1)-th.


-----Output-----

If it is possible to sort the array in ascending order using any sequence of swaps you are allowed to make, print YES. Otherwise, print NO.


-----Examples-----
Input
6
1 2 5 3 4 6
01110

Output
YES

Input
6
1 2 5 3 4 6
01010

Output
NO



-----Note-----

In the first example you may swap a_3 and a_4, and then swap a_4 and a_5.
## Apps Parser

The evaluator uses the following parser to convert each raw stdin/stdout positive test case into typed arguments. The implementation test compares `Solve(...)` return values against the output values returned by this parser.

```python
def parser(input: str, output: str) -> tuple[int, list[int], str, str]:
    lines = [ln.strip() for ln in input.strip().splitlines() if ln.strip() != ""]
    if not lines:
        raise ValueError("Empty input")
    first_tokens = lines[0].split()
    try:
        n = int(first_tokens[0])
    except Exception as e:
        raise ValueError("First token is not an integer n") from e
    a_tokens: list[str] = []
    if len(first_tokens) > 1:
        a_tokens.extend(first_tokens[1:])
    if len(lines) >= 2:
        for ln in lines[1:-1]:
            a_tokens.extend(ln.split())
    if len(a_tokens) < n:
        all_tokens = input.strip().split()
        collected: list[str] = []
        for tok in all_tokens[1:]:
            if tok.lstrip("-").isdigit():
                collected.append(tok)
                if len(collected) >= n:
                    break
        if len(collected) >= len(a_tokens):
            a_tokens = collected
    if len(a_tokens) < n:
        raise ValueError("Malformed input: not enough array elements")
    try:
        a = [int(x) for x in a_tokens[:n]]
    except Exception as e:
        raise ValueError("Array elements are not all integers") from e
    if len(lines) < 2:
        raise ValueError("Malformed input: missing string s")
    s_line = lines[-1]
    s = "".join((ch for ch in s_line if ch in "01"))
    out = output.strip()
    return (n, a, s, out)
```
