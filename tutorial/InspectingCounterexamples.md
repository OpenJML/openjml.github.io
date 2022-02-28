---
title: JML Tutorial - Inspecting Counterexamples
---

In normal operation, if openjml detects a verification failure, it simply reports information about the kind and location of the failure. But there is additional information under the hood.

The first bit of evidence to consider is the name of the assertion failure. For example a `NegativeArraySize` failure indicates that an attempt was made to allocated an array, but the size given was negative. A table of all such types of verification failures is given in the OpenJML Users' Guide.

## show statement

A failed proof means that the prover found some set of input values that caused a violation of some assertion. So an easy first step is to ask for the values of relevant program variables. To use our favorite little problem again, consider
```
// openjml --esc T_show1.java
public class T_show1 {
  int abs(int i) {
    int a = i > 0 ? i : -i;
    return a;
  }
}
```
which produces
```
T_show1.java:4: verify: The prover cannot establish an assertion (ArithmeticOperationRange) in method abs: (int negation)
    int a = i > 0 ? i : -i;
                        ^
1 verification failure
```
Now if we insert a `show` statement, we can see an example of values that produce the problem.
```
// openjml --esc T_show2.java
public class T_show2 {
  int abs(int i) {
    //@ show i, -i, (int)-i;
    return  i > 0 ? i : -i;
  }
}
```
which produces
```
```






_Last modified: 2022-02-28 00:00:08_