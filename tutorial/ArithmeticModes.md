# Arithmetic Modes

If you have tried verifying some programs of your own that involve arithmetic,
will will likely have encountered arithmetic overflow errors. This lesson
describes how to work with those.

Arithmetic in Java is 2's-complement arithmetic, modulo 32- or 64- bits.
Java gives no warning if arithmetic operations overflow or underflow.
Thus in Java `x+1` of an integer `x` is not necessarily larger than `x`.
Programmers using Java (or C for that matter) usually ignore the possibility
of integer overflow, informally reasoning that in the intended use of the
program no numbers large enough to cause overflow will be used.
Of course, one purpose of specification and verification is to document 
under just which conditions a program behaves as expected.

Because it is not anticipated, if overflow happens it is likely a bug.
This is not always the case. Code that generates psuedo-random numbers or
performs encryption or compression often intentionally uses overflow. But 
such uses are less common. Thus JML is designed to, by default, warn about
potential overflows in Java code.

On the other hand, readers of specifications generally interpret them
as mathematical---that is, that specifications use infintie precision arithmetic.[^1]

[^1]: These design elements of JML arise from the research work in 
Chalin, P.: Logical foundations of program assertions: What do practitioners want? In: Pro-ceedings of the 3rd International Conference on Software Engineering and Formal Method(SEFM). IEEE Computer Society, Los Alamitos, California (2005).

Consequently, JML defines three *arithmetic modes* (for integer arithmetic):

* Java mode: arithmetic behaves precisely as in Java, with silent warp-around of operations
* Safe mode: the results of arithmetic operations are the same as in Java mode, but verification errors are issued if the operation may overflow
* Math (bigint) mode: Values and operations are in mathmatical arithmetic.

The default is *safe mode* for expressions in Java code and *meth mode* for
expressions in specifications. There are ways to specify the mode to be used,
described below.

First an example. The simple code
```
// openjml -esc T_arithmetic1.java
public class T_arithmetic1 {
  //@ ensures \result == i+1;
  public int increment(int i) {
    return i+1;
  }
}
```
gives an error:
```
T_arithmetic1.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method increment: overflow in int sum
    return i+1;
            ^
1 verification failure
```
To avoid this, a preconditino is needed that guards against overflow:
```
// openjml -esc T_arithmetic2.java
public class T_arithmetic2 {
  //@ requires i < Integer.MAX_VALUE;
  //@ ensures \result == i+1;
  public int increment(int i) {
    return i+1;
  }
}
```
verifies without error.

Similarly
```
// openjml -esc T_arithmetic3.java
public class T_arithmetic3 {
  //@ ensures \result >= 0;
  public int abs(int i) {
    return i>= 0 ? i : -i;
  }
}
```
produces
```
T_arithmetic3.java:5: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method abs: (int negation)
    return i>= 0 ? i : -i;
                       ^
1 verification failure
```
while
```
// openjml -esc T_arithmetic4.java
public class T_arithmetic4 {
  //@ requires i !=Integer.MIN_VALUE;
  //@ ensures \result >= 0;
  public int abs(int i) {
    return i>= 0 ? i : -i;
  }
}
```
verifies without error.

One final example is a bug that was present in binary search library code for years. The algorithm rquires computing a value `mid` midway between `low` and `hi`, which are indices into an array. The simple computation, `mid = (lo+hi)/2`
has a potential overflow problem, and would be identified by OpenJML;
the preferred alternative, `mid = lo + (hi-lo)/2` works fine.
We will elaborate this example when discussing [specifying and verifying loops](Loops) in a later lesson.

An alternate design would have the default mode for specification and Java
code both be *Java mode*. But this would hide bugs, since if the potential
overflow in the Java code is missed, it would be missed also in the 
similar code in the specification as in the first example above.
JML's defaults are chosen to highlight potential overflow bugs.

There are a variety of ways to set the arithmetic mode in operation.
* Within a specification expression, subexpressions can be computed with a
specific arithmetic mode using the functions `\java_math(...)`, `\safe_math(...)`, `\bigint_math(...)`.
These each take one argument and return the value aof the argument, but the
argument expression is computed using the given mode. These operatinos are
not available for Java code, because there are no such operations in Java.
* The mode for a proof attempt using OpenJML can be set using command-line options: `-code-math=...` and `-spec-math=...` to set the mode for Java code and specifications, respectively, with possible values of `java`, `safe`, and `bigint`.
For example, to turn off overflow warnings in the Java code one can set the gllbal default using `-code-math=java`
* You can set the mode for a particular method using the modifiers
`code_java_math`, `spec_java_math, `code_safe_math`, etc.
In this example, both the code and specs are computed with java math, so they agree, even when there is an overflow.
```
// openjml -esc T_arithmetic5.java
public class T_arithmetic5 {
  //@ ensures \result == \java_math(i+1);
  //@ code_java_math
  public int m(int i) { 
    return i+1;
  }
}
```
