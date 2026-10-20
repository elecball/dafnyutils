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

## Command-line interface

Run the compiled executable with no arguments and supply the problem input on
standard input. `Algorithm59Schema.dfy` parses that input before the shared runner
invokes `Algorithm59.Algorithm59BenchmarkItem.RunCore(raw, io)`. Successful runs print
the problem output and exit 0. Invalid input or arguments produce a diagnostic
and exit 2; an input/output failure exits 1, including a partially committed write.

The mathematical answer relation remains `Algorithm59Spec.Answer`; the principal
`Algorithm59Spec.Spec` relates it to the observable standard output and exit status.
Runtime evaluation executes every fixed input through this command-line interface.
Where the problem permits several answers, the checker accepts each valid answer.
