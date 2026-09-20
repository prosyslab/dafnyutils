# Algorithm Problem 1

- source: https://codeforces.com/problemset/problem/770/B
- difficulty: interview

## Problem Statement

Anton has the integer x. He is interested what positive integer, which doesn't exceed x, has the maximum sum of digits.

Your task is to help Anton and to find the integer that interests him. If there are several such integers, determine the biggest of them. 


-----Input-----

The first line contains the positive integer x (1 ≤ x ≤ 10^18) — the integer which Anton has. 


-----Output-----

Print the positive integer which doesn't exceed x and has the maximum sum of digits. If there are several such integers, print the biggest of them. Printed integer must not contain leading zeros.


-----Examples-----
Input
100

Output
99

Input
48

Output
48

Input
521

Output
499
## Apps Parser

The evaluator uses the following parser to convert each raw stdin/stdout positive test case into typed arguments. The implementation test compares `Solve(...)` return values against the output values returned by this parser.

```python
def parser(input: str, output: str) -> tuple[int, int]:
    """
    Parse the problem input and output into integers.

    Returns:
      (x, result)
    """
    inp = input.strip().split()
    out = output.strip().split()
    if not inp:
        raise ValueError("Empty input")
    if not out:
        raise ValueError("Empty output")
    x = int(inp[0])
    result = int(out[0])
    return (x, result)
```
