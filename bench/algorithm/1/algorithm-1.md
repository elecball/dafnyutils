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

## Command-line interface

Run the compiled executable with no arguments and supply the problem input on
standard input. `Algorithm1Schema.dfy` parses that input before the shared runner
invokes `Algorithm1.Algorithm1BenchmarkItem.RunCore(raw, io)`. Successful runs print
the problem output and exit 0. Invalid input or arguments produce a diagnostic
and exit 2; an input/output failure exits 1, including a partially committed write.

The mathematical answer relation remains `Algorithm1Spec.Answer`; the principal
`Algorithm1Spec.Spec` relates it to the observable standard output and exit status.
Runtime evaluation executes every fixed input through this command-line interface.
Where the problem permits several answers, the checker accepts each valid answer.
