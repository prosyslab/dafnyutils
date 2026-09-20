# Algorithm Problem 75

- source: https://codeforces.com/problemset/problem/699/B
- difficulty: interview

## Problem Statement

You are given a description of a depot. It is a rectangular checkered field of n × m size. Each cell in a field can be empty (".") or it can be occupied by a wall ("*"). 

You have one bomb. If you lay the bomb at the cell (x, y), then after triggering it will wipe out all walls in the row x and all walls in the column y.

You are to determine if it is possible to wipe out all walls in the depot by placing and triggering exactly one bomb. The bomb can be laid both in an empty cell or in a cell occupied by a wall.


-----Input-----

The first line contains two positive integers n and m (1 ≤ n, m ≤ 1000) — the number of rows and columns in the depot field. 

The next n lines contain m symbols "." and "*" each — the description of the field. j-th symbol in i-th of them stands for cell (i, j). If the symbol is equal to ".", then the corresponding cell is empty, otherwise it equals "*" and the corresponding cell is occupied by a wall.


-----Output-----

If it is impossible to wipe out all walls by placing and triggering exactly one bomb, then print "NO" in the first line (without quotes).

Otherwise print "YES" (without quotes) in the first line and two integers in the second line — the coordinates of the cell at which the bomb should be laid. If there are multiple answers, print any of them.


-----Examples-----
Input
3 4
.*..
....
.*..

Output
YES
1 2

Input
3 3
..*
.*.
*..

Output
NO

Input
6 5
..*..
..*..
*****
..*..
..*..
..*..

Output
YES
3 3
## Apps Parser

The evaluator uses the following parser to convert each raw stdin/stdout positive test case into typed arguments. The implementation test compares `Solve(...)` return values against the output values returned by this parser.

```python
def parser(input: str, output: str) -> tuple[int, int, list[str], str, int, int]:
    in_lines = input.strip().splitlines()
    idx = 0
    while idx < len(in_lines) and in_lines[idx].strip() == "":
        idx += 1
    n = 0
    m = 0
    grid: list[str] = []
    if idx < len(in_lines):
        first = in_lines[idx].strip()
        idx += 1
        parts = first.split()
        if len(parts) >= 2:
            try:
                n = int(parts[0])
                m = int(parts[1])
            except ValueError:
                n = 0
                m = 0
        for _ in range(n):
            row = ""
            if idx < len(in_lines):
                row = in_lines[idx].rstrip("\n").rstrip("\r")
                idx += 1
            if " " in row or "\t" in row:
                row = "".join((ch for ch in row if ch not in (" ", "\t")))
            grid.append(row)
    out_status = "NO"
    out_x = 0
    out_y = 0
    out_tokens = output.strip().split()
    if out_tokens:
        first_tok = out_tokens[0].upper()
        if first_tok == "YES":
            out_status = "YES"
            nums = []
            for tok in out_tokens[1:]:
                try:
                    nums.append(int(tok))
                except ValueError:
                    continue
                if len(nums) == 2:
                    break
            if len(nums) == 2:
                out_x, out_y = (nums[0], nums[1])
        elif first_tok == "NO":
            out_status = "NO"
        else:
            has_yes = any((tok.upper() == "YES" for tok in out_tokens))
            if has_yes:
                out_status = "YES"
                nums = []
                for tok in out_tokens:
                    try:
                        nums.append(int(tok))
                    except ValueError:
                        continue
                    if len(nums) == 2:
                        break
                if len(nums) == 2:
                    out_x, out_y = (nums[0], nums[1])
            else:
                out_status = "NO"
    return (n, m, grid, out_status, out_x, out_y)
```
