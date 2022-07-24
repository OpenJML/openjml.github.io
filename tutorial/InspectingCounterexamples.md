---
title: JML Tutorial - Inspecting Counterexamples
---

In normal operation, if openjml detects a verification failure, it simply reports information about the kind and location of the failure. But there is additional information under the hood.

The first bit of evidence to consider is the name of the assertion failure. For example a `NegativeArraySize` failure indicates that an attempt was made to allocate an array, but the size given was negative. A table of all such types of verification failures is given in the OpenJML Users' Guide.

## show statement

A failed proof means that the prover found some set of input values that caused a violation of some assertion. So an easy first step is to ask for the values of relevant program variables. Consider this example:
```
{% include_relative T_show1.java %}
```
which produces
```
{% include_relative T_show1.out %}
```
So there is an error somewhere. Now if we insert a `show` statement, we can see an example of values that produce the problem.
```
{% include_relative T_show2.java %}
```
which produces
```
{% include_relative T_show2.out %}
```
The values shown are the result of a non-deterministic search; they might very well be different values on subsequent runs.
Nevertheless, for the values of `a`, `b`, `c`, and `d` shown here, the result is equal to `b` or `d`, instead of, for these values, the value of `a`.
Some code inspection shows that there is a cut&paste error on line 9.

The counterexample is always in terms of concrete values --- that is how the underlying solvers work. One would much rather have a symbolic condition that represents the cases that fail, but that is beyond the current state of the art. At present, the best one can do is do some human induction based on a few examples to understand when a program or its specification fails.

A few comments about the `show` statement are in order:
* Any variable names in the `show` statement must be in scope at that position in the program.
* The values are reported as of that position in the program. If we had moved the `show` statement in the above example to an earlier line, the value
of `maxSoFar` would be different.
* You can include expressions in the list of items to show, not just variable names. 
* However, the expressions are evaluated as specification expressions, in other words using mathematical integers (`math_mode`, cf. [the discussion on Arithmetic](ArithmeticModes)) and so might have a different value than the same
expression in Java code.
* The `show` statement must be along the execution path that leads to the violation. For example, if the violation is in the _then_ branch of an if-statement but the `show` statement is in the _else_ branch, the `show` statement will have no effect.
* Evaluation of the program stops when a violation is found. So if the `show` statement is after the line with the violation, it will not result in any output.

To illustrate the last bullet point above, consider
```
{% include_relative T_show3.java %}
```
which yields
```
{% include_relative T_show3.out %}
```
There is no output from the `show` statement because it is after the violation.
Instead if we put the `show` statement first, as in
```
{% include_relative T_show4.java %}
```
we are told
```
{% include_relative T_show4.out %}
```

## \lbl expression

The show statement lets you display values of variables or of computations. But sometimes one needs to see the value of a subexpression in situ,
without recomputing it as one of the shown values.  For this purpose the `\lbl` expression can be used, within specifications.
For example, suppose you have a postcondition `ensures a+b < c+d;` which is failing. You can label some subexpressions as follows:
`ensures (\lbl AB a+b) < (\lbl CD c+d);`.  The `\lbl` expression just passes on its value (like a parenthesized expression), but records the value to report in 
a counterexample. For example, we could try this on the example from the last subsection:
```
{% include_relative T_show2a.java %}
```
producing
```
{% include_relative T_show2a.out %}
```
That information tells us that the problem has to do with inputs `c` and `d`. Note that the example changed from using short-circuiting `&&` to non-short-circuiting `&` and operators. Otherwise if the `\result >= a` conjunct is false, that value is reported, but the rest of the precondition is not evaluated.
Though `\lbl` can be used in any specification expression, it is most useful in method specifications where a `show` statement cannot be placed.


## ghost declarations

JML allows placing _ghost declarations_ (discussed [here](Ghost)) as statements in the body of a method. 
They can also be useful to record values of variables and them compare them to others, `show` them, perform specification-side computations, etc. as part of the debugging process.

## Execution traces: the `--trace` and `--subexpressions` options

Using a `show` statement is handy but is a bit like debugging a program using print statements: you get some data, but you have to still manually review the program to see what might be going wrong, working through the code step by step. An additional openjml tool is the `--trace` option. Upon a failure, it outputs an execution trace ending at the point of the violation. So the first example above, using now `openjml --esc --trace T_show1.java`, produces
```
{% include_relative T_show5.out %}
```
This tells you the execution route to the violation. But more useful is the `--subexpressions` option, which will give additional information.
Using `openjml --esc --subexpressions T_show1.java` we get
```
{% include_relative T_show6.out %}
```
It still takes some manual inspection, but the trace of subexpression values is better than having to do that tracing oneself from the input values provided by `show`.

## Counterexamples

Though the subexpression option above usually provides the most useful information for debugging, it is also possible to dump all the counterexample information.
The `--counterexample` or `-ce` options do this. However, the output is quite verbose and (at present) uses internal encodings of variable names. Improving this information is a planned task, but at the moment the output is useful mainly to experts.


