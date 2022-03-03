---
title: JML Tutorial - Inspecting Counterexamples
---

In normal operation, if openjml detects a verification failure, it simply reports information about the kind and location of the failure. But there is additional information under the hood.

The first bit of evidence to consider is the name of the assertion failure. For example a `NegativeArraySize` failure indicates that an attempt was made to allocate an array, but the size given was negative. A table of all such types of verification failures is given in the OpenJML Users' Guide.

## show statement

A failed proof means that the prover found some set of input values that caused a violation of some assertion. So an easy first step is to ask for the values of relevant program variables. Consider this example:
```
// openjml --esc T_show1.java
public class T_show1 {
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
  //@ ensures \result == a || \result == b || \result == c || \result == d;
  int max(int a, int b, int c, int d) {
    int maxSoFar = a;
    if (b > maxSoFar) maxSoFar = b;
    if (c > maxSoFar) maxSoFar = c;
    if (d > maxSoFar) maxSoFar = c;
    return maxSoFar;
  }
}
```
which produces
```
T_show1.java:10: verify: The prover cannot establish an assertion (Postcondition: T_show1.java:3:) in method max
    return maxSoFar;
    ^
T_show1.java:3: verify: Associated declaration: T_show1.java:10:
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
      ^
2 verification failures
```
So there is an error somewhere. Now if we insert a `show` statement, we can see an example of values that produce the problem.
```
// openjml --esc T_show2.java
public class T_show2 {
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
  //@ ensures \result == a || \result == b || \result == c || \result == d;
  int max(int a, int b, int c, int d) {
    int maxSoFar = a;
    if (b > maxSoFar) maxSoFar = b;
    if (c > maxSoFar) maxSoFar = c;
    if (d > maxSoFar) maxSoFar = b;
    //@ show a, b, c, d, maxSoFar;
    return maxSoFar;
  }
}
```
which produces
```
T_show2.java:10: verify: Show statement expression a has value ( - 2147480361 )
    //@ show a, b, c, d, maxSoFar;
             ^
T_show2.java:10: verify: Show statement expression b has value ( - 2147480362 )
    //@ show a, b, c, d, maxSoFar;
                ^
T_show2.java:10: verify: Show statement expression c has value ( - 2147477363 )
    //@ show a, b, c, d, maxSoFar;
                   ^
T_show2.java:10: verify: Show statement expression d has value ( - 2147477362 )
    //@ show a, b, c, d, maxSoFar;
                      ^
T_show2.java:10: verify: Show statement expression maxSoFar has value ( - 2147480362 )
    //@ show a, b, c, d, maxSoFar;
                         ^
T_show2.java:11: verify: The prover cannot establish an assertion (Postcondition: T_show2.java:3:) in method max
    return maxSoFar;
    ^
T_show2.java:3: verify: Associated declaration: T_show2.java:11:
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
      ^
7 verification failures
```
The values shown are the result of a non-deterministic search; they might very well be different values on subsequent runs.
Nevertheless, it appears that the value of `maxSoFar`, which is the value returned, is the same as `c`, or perhaps the max of `a`, `b`, and `c`,
and does not take `d` into account. Some code inspection shows that there is a cut&paste error on line 9.

The counterexample is always in terms of concrete values --- that is how the underlying solvers work. One would much rather have a symbolic condition that represents the cases that fail, but that is beyond the current state of the art. At present, the best one can do is do some human induction based on a few examples to understand when a program or its specification fails.

A few comments about the `show` statement are in order:
* Any variable names in the show statement must be in scope at that position in the program.
* The values are reported as of that position in the program. If we had moved the `show` statement in the above example to an earlier line, the value
of `maxSoFar` would be different.
* You can include expressions in the list of items to show, not just variable names. 
* However, the expressions are evaluated as specification expressions, in other words using mathematical integers (`math_mode`, cf. [the discussion on Arithmetic](ArithmeticModes)) and so might have a different value than the same
expression in Java code.
* The `show` statement must be along the execution path that leads to the violation. For example, if the violation is in the then branch of an if-statment but the show statement is in the else branch, the show statement will have no effect.
* Evaluation of the program stops when a violation is found. So if the `show` statement is after the line with the violation, it will not result in any output.

To illustrate the last bullet point above, consider
```
// openjml --esc T_show3.java
public class T_show3 {
  //@ public invariant data.length >= 10;
  //@ spec_public
  private int[] data = new int[10];
  //@ requires i >= 0;
  public int data(int i) {
    int r = data[i];
    //@ show i, r;
    return r;
  }
}

```
which yields
```
T_show3.java:8: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method data
    int r = data[i];
                ^
1 verification failure
```
There is no output from the `show` statement because it is after the violation.
Instead if we put the `show` statement first, as in
```
// openjml --esc T_show4.java
public class T_show4 {
  //@ public invariant data.length >= 10;
  //@ spec_public
  private int[] data = new int[10];
  //@ requires i >= 0;
  public int data(int i) {
    //@ show i, data.length;
    int r = data[i];
    return r;
  }
}

```
we are told
```
T_show4.java:8: verify: Show statement expression i has value 1807
    //@ show i, data.length;
             ^
T_show4.java:8: verify: Show statement expression data.length has value 1806
    //@ show i, data.length;
                ^
T_show4.java:9: verify: The prover cannot establish an assertion (PossiblyTooLargeIndex) in method data
    int r = data[i];
                ^
3 verification failures
```

## Execution traces: the `-`trace` and `--subexpressions` options

Using a `show` statement is handy but is a bit like debugging a program using print statements: you get some data, but you have to still manually review the program to see what might be going wrong, working through the code step by step. An additional openjml tool is the `--trace` option. Upon a failure, it outputs an execution trace ending at the point of the violation. So the first example above, using now `openjml --esc --trace T_show1.java`, produces
```
T_show1.java:10: verify: The prover cannot establish an assertion (Postcondition: T_show1.java:3:) in method max
    return maxSoFar;
    ^
T_show1.java:3: verify: Associated declaration: T_show1.java:10:
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
      ^

TRACE of T_show1.max(int,int,int,int)
T_show1.java:1: 	requires true; 
T_show1.java:6: 	int maxSoFar = a
T_show1.java:7: 	if (b > maxSoFar) ...
				Condition = true
T_show1.java:7: 	maxSoFar = b
T_show1.java:8: 	if (c > maxSoFar) ...
				Condition = true
T_show1.java:8: 	maxSoFar = c
T_show1.java:9: 	if (d > maxSoFar) ...
				Condition = true
T_show1.java:9: 	maxSoFar = c
T_show1.java:10: 	return maxSoFar;
T_show1.java:3: 	ensures \result >= a && \result >= b && \result >= c && \result >= d; 
T_show1.java:10: Invalid assertion (Postcondition)
: T_show1.java:3: Associated location

2 verification failures
```
This tells you the execution route to the violation. But more useful is the `--subexpressions` option, which will give additional information.
Using `openjml --esc --subexpressions T_show1.java` we get
```
T_show1.java:10: verify: The prover cannot establish an assertion (Postcondition: T_show1.java:3:) in method max
    return maxSoFar;
    ^
T_show1.java:3: verify: Associated declaration: T_show1.java:10:
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
      ^

TRACE of T_show1.max(int,int,int,int)
T_show1.java:1: 	requires true; 
			VALUE: true	 === true
T_show1.java:6: 	int maxSoFar = a
			VALUE: a	 === ( - 8946 )
			VALUE: maxSoFar	 === ( - 8946 )
T_show1.java:7: 	if (b > maxSoFar) ...
			VALUE: b	 === ( - 8945 )
			VALUE: maxSoFar	 === ( - 8946 )
			VALUE: b > maxSoFar	 === true
			VALUE: (b > maxSoFar)	 === true
				Condition = true
T_show1.java:7: 	maxSoFar = b
			VALUE: b	 === ( - 8945 )
			VALUE: maxSoFar = b	 === ( - 8945 )
T_show1.java:8: 	if (c > maxSoFar) ...
			VALUE: c	 === 1
			VALUE: maxSoFar	 === ( - 8945 )
			VALUE: c > maxSoFar	 === true
			VALUE: (c > maxSoFar)	 === true
				Condition = true
T_show1.java:8: 	maxSoFar = c
			VALUE: c	 === 1
			VALUE: maxSoFar = c	 === 1
T_show1.java:9: 	if (d > maxSoFar) ...
			VALUE: d	 === 2
			VALUE: maxSoFar	 === 1
			VALUE: d > maxSoFar	 === true
			VALUE: (d > maxSoFar)	 === true
				Condition = true
T_show1.java:9: 	maxSoFar = c
			VALUE: c	 === 1
			VALUE: maxSoFar = c	 === 1
T_show1.java:10: 	return maxSoFar;
			VALUE: maxSoFar	 === 1
T_show1.java:3: 	ensures \result >= a && \result >= b && \result >= c && \result >= d; 
			VALUE: \result	 === 1
			VALUE: a	 === ( - 8946 )
			VALUE: \result >= a	 === true
			VALUE: \result	 === 1
			VALUE: b	 === ( - 8945 )
			VALUE: \result >= b	 === true
			VALUE: \result >= a && \result >= b	 === true
			VALUE: \result	 === 1
			VALUE: c	 === 1
			VALUE: \result >= c	 === true
			VALUE: \result >= a && \result >= b && \result >= c	 === true
			VALUE: \result	 === 1
			VALUE: d	 === 2
			VALUE: \result >= d	 === false
T_show1.java:10: Invalid assertion (Postcondition)
: T_show1.java:3: Associated location

2 verification failures
```
It still takes some manual inspection, but the trace of subexpression values is better than having to do that tracing oneself from the input values provided by `show`.

## Counterexamples

Though the subexpression option above usually provides the most useful information for debugging, it is also possible to dump all the counterexample information.
The `--counterexample` or `-ce` options do this. However, the output is quite verbose and (at present) uses internal encodings of variable names. Improving this information is a planned task, but at the moment the output is useful mainly to experts.


_Last modified: 2022-03-02 20:15:13_