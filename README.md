# Homework 5

### Limitations

- Liveness does not consider registers used by other instructions (like idiv,
  calls and the registers already present in the code)
- Liveness does not consider offsets (for example, in 16(%rax), %rax is not 
  considered live)
- There is no spilling: if graph coloring fails, it will throw an error
- For a reason I wasn't able to figure out, recursive calls do not work 
  (they cause a segmentation fault)

The above will make most example programs not work (they either segfault or 
continuously loop). One that is known to work is print.

During compilation, the Scala compiler might throw a stack overflow exception. 
Make sure to give it enough stack space (I gave 4MB).

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
