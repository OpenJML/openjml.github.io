---
title: JML Tutorial - Specifying Exceptions
---

JML can specify exception execution paths just as well as normal execution paths.
A normal execution has associated postconditions --- `ensures` clauses.
OpenJML verifies that if the method exits normally,
then the postcondition must be true.
Similarly exits with exceptions use an exceptional postcondition,
which is a `signals` clause in JML.
A `signals` clause has this syntax: `signals (E e) P;`
where `E` is some exception type (derived from `java.lang.Exception`,
although it could be `java.lang.Exception` itself),
`e` is an identifier, which stands for the exception object and can thus be used in the predicate `P`.
The meaning of such a signals clause is:
if the method terminates with an exception derived from `E`,
then the given predicate must be true.
(In JML one does not specify behavior regarding Java Errors,
as these are mostly unrecoverable system errors like `OutOfMemoryError`
or `StackOverflowError`.)

So we could write this trivial example:
```
{% include_relative T_Exception1.java %}
```
which verifies successfully. Note that the specification includes a second kind of clause, the `signals_only` clause.
This clause specifies the kinds of exceptions that may be thrown from the method.
Unlike Java, JML requires that a `signals_only` clause list runtime exceptions (derived from `java.lang.RuntimeException`), so that each specification is clear about what exceptions might be thrown.

However, if the `signals_only` clause is omitted, then the default is as if there was a `signals_only` clause that lists `java.lang.RuntimeException`
and any declared (checked) exception types.

If we specify that no exceptions can be thrown,
with the clause `signals_only \nothing`,
then a verification failure results if any exceptions can be thrown
as shown in the following example (and its output with extended static checking).
```
{% include_relative T_SpecifyingExceptionsNone.java %}

```
which when checked with ESC produces the following.
```
{% include_relative T_SpecifyingExceptionsNone.out %}

```
OpenJML complains about the above code since the specification prohibits exceptions from being thrown.

Verification failures can also occur due to such (runtime) conditions as null pointer exceptions (when `nullable_by_default` is used), 
as the following example shows.
```
{% include_relative T_Exception1a.java %}
```
```
{% include_relative T_Exception1a.out %}
```

In order to say that a particular type of exception is never thrown,
use a `signals` clause (for that exception type) with a `false` predicate.
Then the `signals` clause means --- if an exception is thrown then `false` --- which is equivalent to saying
"if false is true, then throwing such an exception is correct",
thus equivalently: "such an exception may not be thrown".

For example, the following specifies that no exceptions can be thrown by the method `value`, due to the `signals` clause that uses the overall type `Exception` as the exception type and which specifies that an exception may only be thrown when `false` is true.
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

## **[Exercises](https://www.openjml.org/tutorial/exercises/SpecifyingExceptionsEx.html)**

Follow the link in the above heading to work on the exercises on this topic.
