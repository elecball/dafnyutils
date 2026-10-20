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

## Command-line interface

Run the compiled executable with no arguments and supply the problem input on
standard input. `Algorithm20Schema.dfy` parses that input before the shared runner
invokes `Algorithm20.Algorithm20BenchmarkItem.RunCore(raw, io)`. Successful runs print
the problem output and exit 0. Invalid input or arguments produce a diagnostic
and exit 2; an input/output failure exits 1, including a partially committed write.

The mathematical answer relation remains `Algorithm20Spec.Answer`; the principal
`Algorithm20Spec.Spec` relates it to the observable standard output and exit status.
Runtime evaluation executes every fixed input through this command-line interface.
Where the problem permits several answers, the checker accepts each valid answer.
