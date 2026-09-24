# Bug Analysis

> What is this about ?

This folder contains detailed analysis of major bugs in TACO, and what their
potential impacts were. While TACO will probably not be used on any production
grade algorithm soon, some users still might find this valuable information, in
case they want to start implementing their own model checkers.

## Terminology

In the bug reports, we will categorize the impact of bugs into three classes:

- **Crash Bugs**: Bugs that will simply cause TACO to fail, without reporting
  any verification result to the user.
- **Soundness Bugs**: Bugs that lead to the reporting of invalid or incomplete
  counter examples.
- **Completeness Bugs**: Bugs can lead to TACO missing a potential counter
  example.
