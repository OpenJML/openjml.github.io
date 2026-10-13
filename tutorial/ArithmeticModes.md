---
title: JML Tutorial - Arithmetic and Arithmetic Modes
---

If you have tried verifying some programs of your own that involve arithmetic,
you will likely have encountered arithmetic overflow errors. This lesson
describes how to specify arithmetic modes to prevent those errors.

Integer arithmetic in Java code is 2's-complement arithmetic, modulo 32- or 64- bits (for `int` or `long`),
with values sometimes being truncated to only 16 or 8 bits (for types `short` or `char`).
Java's arithmetic is defined to give no warning if arithmetic operations overflow
or underflow or if conversions lose high-order bits.
Thus in Java, for an `int x` (or `long x`), `x+1`
is _not_ necessarily larger than `x`.
Programmers using Java often ignore the possibility
of such overflows, informally reasoning that in the intended use of the
program no numbers large enough to cause overflow will be used.
However, one purpose of specification and verification is to document 
the precise conditions under which a program behaves as expected.

JML is designed to, by default, warn about potential overflows in Java code.
Although JML takes the position that such overflows indicate a possible bug,
that is not always the case.
For example, code that generates psuedo-random numbers or
performs encryption or compression often intentionally uses overflow. But 
such uses are less common. 

On the other hand, readers of _specifications_ generally interpret expressions
mathematically---that is, readers interpret specifications as using mathematical (i.e., infinite precision) arithmetic.[^1]

Consequently, JML defines three *arithmetic modes* (for integer arithmetic):

* Java mode: arithmetic behaves precisely as in Java, with silent wrap-around of overflowing and underflowing operations, which are not considered errors,
* Safe mode: the results of arithmetic operations are the same as in Java mode, but verification errors are issued if the operation may over/underflow
* Math (bigint) mode: Values and operations are the same as in mathematics---values are unbounded and so there is no over/underflow.

The default in JML is to use *safe mode* for expressions in Java code
but *math mode* (i.e., bigint mode) for expressions in specifications.
(We describe several ways to specify the arithmetic mode to be used below.)

First an example. The following simple code
```
{% include_relative T_arithmetic1.java %}
```
produces several errors:
```
{% include_relative T_arithmetic1.out %}
```
To avoid these overflow errors, one can use an assumption (or a [precondition](Preconditions)) to guard against the potential overflow. The following thus verifies without error.
```
{% include_relative T_arithmetic2.java %}
```

Similarly
```
{% include_relative T_arithmetic3.java %}
```
produces the following errors (because `Integer.MIN_VALUE` has no positive counterpart in the 2's-complement integer representation used by Java).
```
{% include_relative T_arithmetic3.out %}
```

However, the following verifies without error, due to the added assumption
(which might be recorded as a [precondition](Preconditions)) that guards against the potential overflow.
```
{% include_relative T_arithmetic4.java %}
```

### Overflows in Intermediate Computations

One final example is a bug that was present in Java's binary search library code for years.[^2] The binary search algorithm requires computing a value `mid` that is midway between `low` and `hi`, which are indices into an array.
The simple computation `mid = (lo+hi)/2;` has a potential overflow problem,
and OpenJML would issue an error for the potential overflow;
however, the alternative `mid = lo + (hi-lo)/2;` does not have that potential overflow.
We will elaborate this example when discussing [specifying and verifying loops](Loops) in a later lesson.

### Design Alternatives

An alternate design of JML would have the default mode for specification and Java
code both be *Java mode*. But this would hide bugs, since if the potential
overflow in the Java code is missed, it likely would be missed also in the 
specification, as in the first example above.
JML's defaults are chosen to highlight potential overflow bugs.

## Setting the Arithmetic Mode

There are a variety of ways to set the arithmetic mode in JML:
* Within a specification expression, subexpressions can be computed with a
specific arithmetic mode using the functions `\java_math(...)`, `\safe_math(...)`, or `\bigint_math(...)`.
These functions each take one argument and return the value of the argument, but the
argument expression is computed using the given mode. These operations are
not available for Java code, because there are no such operations in Java.
(In Java one could use the type `BigInteger` to obtain arbitrary precision integer computations, but there is no built-in way to receive warnings about overflows like JML's safe-math mode.)
* The mode for a proof attempt using OpenJML can be set using command-line options: `--code-math=...` and `--spec-math=...` to set the mode for Java code and specifications, respectively, with possible values of `java`, `safe`, and `bigint`.
For example, to turn off overflow warnings in the Java code one can set the global default using `--code-math=java`
* You can set the mode for a particular method using the modifiers
`code_java_math`, `spec_java_math`, `code_safe_math`, `spec_safe_math` and `spec_bigint_math` (note that there is no such thing as `code_bigint_math`, since that would change the meaning of the Java code).

In the following example, both the code and specs are computed with Java math,
 so they agree, even when there is an overflow; thus this example verifies.

```
{% include_relative T_arithmetic5.java %}
```

## **[Exercises](https://www.openjml.org/tutorial/exercises/ArithmeticEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_arithmetic1 file](T_arithmetic1.java)
+ [T_arithmetic2 file](T_arithmetic2.java)
+ [T_arithmetic3 file](T_arithmetic3.java)
+ [T_arithmetic4 file](T_arithmetic4.java)
+ [T_arithmetic5 file](T_arithmetic5.java)

## Footnotes

[^1]: These design elements of JML arise from the research reported in [Chalin, P.: Logical foundations of program assertions: What do practitioners want?](https://ieeexplore.ieee.org/document/1575928) In _Proceedings of the 3rd International Conference on Software Engineering and Formal Method (SEFM)_. IEEE Computer Society, Los Alamitos, California (2005).

[^2]: See Bloch, Joshua, "Extra, Extra - Read All About It: Nearly All Binary Searches and Mergesorts are Broken" in [Google Research Blog post](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/), June 2, 2006.

