# Homework 6 - Floating point

The goal of this assignment is to implement floating point operations.

To do this, the type `float` is introduced.
Float literals have the form `[0-9]+.[0-9]+`: we have two groups of digits,
separated by a dot. The dot must be preceded and followed by at least one digit.
Examples: `0.43`, `32.01`.

A `float` cannot be assigned to an `int` and vice versa.
However, some arithmetic operations allow both `float` and `int`, at the same
time: these operators are: `+`, `-`, `*`, `/`, `<`, `<=`, `>`, `>=`, `==`, `!=`.
When used with different types, the arithmetic operators will return a `float`,
while the comparison operators will still return a `boolean`.

`float`s can be passed to functions, specified as return types from functions
and used as base types for arrays, just like `int`s.

An example Ristretto source file which demonstrates floating point operations
can be found in the `examples` folder, called `float.r`.

### Notes and limitations

- The commands for the Ristretto compiler did not change from the previous
  assignment.
- During compilation, the Scala compiler might throw a stack overflow exception. 
  Make sure to give it enough stack space (I gave 4MB).
- This assignment does not include the improvements from Assignment 5.
- **Regression:** String literals do not work anymore.
- Floating point literals are hardcoded into `movq` instructions instead of
  being placed at the end of a program/procedure using `.long` (which is what
  GCC does).

# Ristretto

This is a compiler for a small language called Ristretto, consisting of integer
and boolean expressions and statements, arrays, and functions.

The language is based on the Xi language by Andrew Myers,
used in his compiler class at Cornell.

The design of the compiler is based on the MiniJava compiler
by Jens Palsberg. Each phase of the compiler has a concrete syntax
that can be used as input to the next phase. This makes it easier
to break the compiler up into digestible parts for a class.
In particular, it is not required that a previous phase of the compiler
be completely working for the next phase to be implemented.
