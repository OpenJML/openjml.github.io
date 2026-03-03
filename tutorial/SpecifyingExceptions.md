---
title: JML Tutorial - Specifying Exceptions
---

JML can specify exception execution paths just as well as normal execution paths.
A normal execution has associated postconditions --- `ensures` clauses. The logic is --- if the method exits normally, then the postcondition must be true.
Similarly exits with exceptions use an exceptional postcondition --- `signals` clauses.
A `signals` clause has this syntax: `signals (E e) <expression>`
where `E` is some exception type (derived from or the same as `java.lang.Exception`).
The meaning of this clause is --- if the method terminates with an exception derived from `E`, then the given expression must be true.
[ JML does not specify behavior regarding Java Errors as these are mostly unrecoverable system errors like OutOfMemoryError or StackOverflowError.]

So we could write this trivial example:
```
{% include_relative T_Exception1.java %}
```
which verifies successfully. Note that the specification includes a second kind of clause, the `signals_only` clause.
This clause specifies the kinds of exceptions that may be thrown from the method. 
JML requires the specification to list `RuntimeException`, even though Java does not require declaring `RuntimeException` in a throws clause,
in order to make it explicitly clear what exceptions might be thrown.

If we omit any exceptions, by using the default `signals_only` clause
(`signals_only \nothing`), a verification failure results.
```
{% include_relative T_Exception1a.java %}
```
```
{% include_relative T_Exception1a.out %}
```

The `signals_only` specification comes explicitly into play when the program wants to throw an exception. Consider the following incorrect implementation:
```
{% include_relative T_Exception1b.java %}
```
It produces the output
```
{% include_relative T_Exception1b.out %}
```
Here the method explictly throws an exception, but as that exception is not specified to be thrown, so OpenJML complains.


In order to say that a particular exception is never thrown,
use a `signals` clause (for that exception type) with a `false` predicate.
Then the `signals` clause means --- if an exception is thrown then `false` --- which is equivalent to saying
"if false is true, then throwing such an exception is correct",
thus equivalently: "such an exception may not be thrown".

Here is an example, with the overall type `Exception` as the exception type:
```
{% include_relative T_Exception2.java %}
```
But trying to verify this example produces a verification failure:
```
{% include_relative T_Exception2.out %}
```
as it should. We can guard against an exception by requiring that the method always be called with a non-null argument:
```
{% include_relative T_Exception3.java %}
```
which now verifies again.

Exceptional postcondition clauses can be stated in any order;
there is no meaning to one being before the other as all must be satisfied.
Consider this example in which there are two kinds of exceptions thrown.
```
{% include_relative T_Exception4.java %}
```
In the second `signals` clause, the expression `a != null` is required; without it, the later expression
`a[i]` is not [well-defined](WellDefinedExpressions). It is immaterial that there is a test for `a` being null
in the other `signals` clause. Note that if there are no `signals` clauses, then OpenJML complains that
some expected conditions cannot be proved, as shown in this example:
```
{% include_relative T_Exception4a.java %}
```
which gives this result
```
{% include_relative T_Exception4a.out %}
```
The three verification failure messages may occur in any order.
This balance between verification failures and exception specifications is an
advanced topic discussed [here](JavaErrorsAndExceptions).


## **[Specifying Exceptions Problem Set](https://www.openjml.org/tutorial/exercises/SpecifyingExceptionsEx.html)**
