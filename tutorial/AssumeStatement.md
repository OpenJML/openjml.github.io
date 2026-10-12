---
title: JML Tutorial - Assume statements
---

## Assume Statements

Like an `assert` statement, an `assume` statement may be used in the
body of a method. The effect of an assume statement is to instruct
the verification engine to assume, *without proof*, that the given 
predicate is true. Such statements can be used to introduce
facts that are too difficult for the proof engine to prove
(for example, as OpenJML uses SMT solvers for its proofs, such statements might include theorems involving multiplication or division).

Assume statements can also be used in other ways. For example, they can be used to temporarily summarize the effect of preceding code 
for the purpose of attempting to prove later code.
When used in this way, one should go back later
to work with the preceding code until the assumption is successfully 
proven and the assume statement can be removed.
(An assume statement can also be replaced with an assert statement; either to test whether OpenJML can prove the predicate is true or to use the assert statement as documentation.)

An example of the basic use of assume statements is seen in the following code.

```Java
{% include_relative  T_assume1.java %}
```

The idea of the `findZeroElement` method is to return an index into the array argument (`a`) that holds 0.
The code is a linear search to compute that index.
However, we don't know yet
[how to specify the behavior of loops](Loops), so we add an
assumptions that we expect to be true.
With that assumption, the above example verifies.

Do you see why the assumption in the example may not always be true?
This shows is the danger of assume statements;
while they can be very helpful in developing a proof,
if the given predicate is not always true,
then one can prove _invalid_ specifications or _incorrect_ implementations.
You can even see that in the example above: if the array `a` does not
contain any elements, then the predicate in the assume statement will be false;
so the code cannot always return an index into `a` of an element holding 0.
Do you see why the code needs `a` to have an element holding 0?
Do you see why the assume statement in the code might be false in that case?

The situation can even be worse. Consider the following drastic, if trivial, case.
```Java
{% include_relative  T_assume2.java %}
```

The assert statement above is explicitly false. So OpenJML
will always report that the assertion is not provable and will produce 
the following output.

```Java
{% include_relative  T_assume2.out %}
```

But suppose we add erroneous assume statements, such as the ones shown that contradict each other as in the following. (This may not be so obvious in practice, since the first assume statement might arise from the method's [precondition](Preconditions), which is assumed at the start of the method.)

```
{% include_relative  T_assume3.java %}
```

In this case OpenJML issues no verification errors. The effect is just like 
the situation in logic where, once a contradiction is assumed, anything,
even false statements, can be proven.

Thus, to emphasize the point: assume statements can be very helpful in the course of developing 
a specification and proof of a method implementation,
but if the OpenJML proof engine can prove them,
then they should be replaced with assert statements.
In any case it is safest to either replace all the assume statements with assert statements or to independently prove that the assume statements are true,
before a verification can be trusted.

## **[Exercises](https://www.openjml.org/tutorial/exercises/AssumeEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_assume1 file](T_assume1.java)
+ [T_assume2 file](T_assume2.java)
+ [T_assume3 file](T_assume3.java)
