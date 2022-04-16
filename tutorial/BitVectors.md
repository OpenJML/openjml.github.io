---
title: JML Tutorial - Reasoning about bit-wise operations
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

In Java programs (and other languages), integer-like variables of various bit-widths are sometimes
used as limited range numbers and sometimes as a collection of bits. For example, the variable
may represent a collection of boolean options, each one as a bit, and all together collected into an
8- or 16- or 32- or 64-bit variable. Java has some bit-wise operations for this purpose: bit-wise and, or and exclusive or, and bit-shift left and right.

This would be transparent to verification except for some limitations of solvers. 
* Current solvers can treat variables as either numbers or bit-vectors but they cannot convert between them.
* Current solvers do not have general bit operations on numbers, only on bit-vectors. Some limited operations can be emulated: for example shifting by a fixed, known amount can be accomplished by multiplication or division. Solvers do implement numeric operations (addition, etc.) for bit-vectors.
* In general, solving logic problems over bit-vectors takes far longer than solving the equivalent problem over numbers, especially on 64-bit longs. Note that this is the reverse of the situation
for implementation code: in Java code, bit-vector operations are sometimes used because they
are faster than the corresponding numeric operations (e.g., right shifts are faster than divides).
* OpenJML has the additional current limitation that it translates a whole method either as bit-vectors or as numbers, and not a mixture.

Because of the above considerations, a choice has to be made: should the int-like values in a given proof attempt be translated as bit-vectors or as numbers. Because performance is usually better, OpenJML by default will attempt to verify a method using numbers for the int-like variables, and only use bit-vectors if there are bit-vector operations that
cannot be performed on numbers.

The choice between using bit-vectors or not is performed automatically, but the user can force the
choice using the command-line option `--esc-bv=true` to use bit-vectors and `--esc-bv=false` to use numbers
(the default is `--esc-bv=auto`).

The following example verifies successfully, but takes 8-10 times longer (on my machine using Z3 4.3.1) using bitvectors vs not.
```
(% include_relative T_BVMult.java %)
```

The important point for writing specifications is that in situations where using bit-vectors is
a performance problem, one wants to keep as much of the program as possible using numbers.
To do that, use the following trick: even if the implementation of method A uses bit-vector operations, 
write the specification so it does not. Then any method B that calls the method A only 
sees numeric operations in A's specification (and not the bit-vector operations in 
A's implementation), so method B does not need to be verified using bit-vectors. The bit-vector
proof is limited to method A.

The following method rounds a number up to the next highest multiple of 16. The implementation
using a non-obvious bit-twiddling trick to do so. The specification expresses the desired
outcome more clearly and uses only numeric operations. The successful verification shows that
the bit-twiddling trick correctly implements the desired result.
```
(% include_relative T_BVRoundUp.java %)
```