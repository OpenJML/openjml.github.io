---
title: JML Tutorial - Assume statements (assume clauses)
---

Preconditions in JML (the predicates in `requires` clauses) are assumed by JML
to hold when verifying a method.
That is, for purposes of verifying a method body, a precondition is equivalent to using an `assume` statement at the beginning of the method body to assume that the precondition holds.
However, preconditions are verified to hold at calls sites,
while assume statements within a method body need are not verified to be true
(either at runtime or during static verification).

## Assume Statements

Like an `assert` statement, a JML  `assume` statement may be used in the
body of a method. The effect of an `assume` statement is to instruct
the verification engine to assume, *without proof*, that the given 
predicate is true. Such statements can be used to introduce
facts that are too difficult for the proof engine to prove.
They can also be used to temporarily summarize the effect of preceding code 
for the purpose of attempting to prove later code; then one goes back later
to work with the preceding code until the assumption is successfully 
proven and the `assume` statement can be removed.

For example, consider the following code:
```
{% include_relative  T_assume1.java %}
```

Here we have stated a postcondition we want in the ensures clause and a sketch
of an implementation to compute it. But we don't know yet how to 
specify the behavior of loops (that is coming [later!](Loops)), so we add some 
assumptions that we expect to be true. With those assumptions, the
above example verifies.

Do you see why the assumptions in the example are not always true?
This is the danger of `assume` statements; while they
can be very helpful in developing a proof,
if the given predicate is not always true,
then it will be possible to prove invalid specifications or implementations.
You can even see that in the example above: if the array `a` does not
contain any elements, then the `assume` statements will be
false; thus the postcondition is incorrect.

The situation can even be worse. Consider the following drastic, if trivial, case.
```
{% include_relative  T_assume2.java %}
```
Here we have an `assert` statement that is explicitly false. So the verifier
will always report that the assertion is not provable and will produce 
this output:
```
{% include_relative  T_assume2.out %}
```

But now we add an erroneous `assume` statement, one that contradicts the
precondition. Remember that the precondition is assumed at the start of a 
method implementation and that the `assume` statement
is also silently assumed at its location in the body.
```
{% include_relative  T_assume3.java %}
```
Now OpenJML issues no verification errors. The effect is just like 
the situation in logic where once a contradiction is assumed, anything,
even false statements, can be proven.

Thus, to emphasize the point: `assume` statements can be very helpful in the course of developing 
a specification and proof of a method implementation,
but if the OpenJML proof engine can prove them,
then they should be replaced with `assert` statements
or removed altogether before a verification is considered sound.

## **[Assume Statements Problem Set](https://www.openjml.org/tutorial/exercises/AssumeEx.html)**

