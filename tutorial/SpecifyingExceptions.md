---
title: JML Tutorial - Specifying Exceptions
---

JML can specify exception execution paths as well as normal execution paths.
A normal execution is specified with one or more [ensures clauses](Postconditions).
An ensures clause specifies that if the method exits normally,
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

So we could write the following trivial example with does verify.
```
{% include_relative T_Exception1.java %}
```

### Specifying what Exceptions may be Thrown: signals_only Clauses

Note that the specification includes a second kind of clause,
the `signals_only` clause.
This clause specifies the kinds of exceptions that may be thrown from the method.
Unlike Java, JML requires that a `signals_only` clause list all exceptions that may occur, including runtime exceptions (derived from `java.lang.RuntimeException`), so that each specification is clear about what exceptions might be thrown.

However, if the `signals_only` clause is omitted, then the default is as if there was a `signals_only` clause that lists `java.lang.RuntimeException`
and all of the exception types declared in the method's header 
(the latter are often called "checked" exceptions).

We can specify that no exceptions can be thrown,
with the clause `signals_only \nothing`,
then a verification failure results if any exceptions can be thrown
as shown in the following example.

```Java
{% include_relative T_SpecifyingExceptionsNone.java %}

```

When the above is checked using OpenJML's extended static checking (ESC)
it produces the following output, since the specification prohibits exceptions from being thrown.

```Java
{% include_relative T_SpecifyingExceptionsNone.out %}

```

Verification failures can also occur due to such (runtime) conditions as null pointer exceptions (when `nullable_by_default` is used), 
as the following example shows.
```Java
{% include_relative T_Exception1a.java %}
```

The above produces the following output when checked with ESC.

```Java
{% include_relative T_Exception1a.out %}
```

### Specifying a Type of Exceptions that cannot be Thrown

In order to say that a particular type of exception is never thrown,
use a `signals` clause (for that exception type) with a `false` predicate.
Then the `signals` clause says that, if that type of exception is thrown,
then `false`, which is equivalent to specifying that such an exception may not be thrown.

For example, the following specifies that no exceptions can be thrown by the method `value`, due to the `signals` clause that uses the overall type `Exception` as the exception type.

```Java
{% include_relative T_Exception2.java %}
```

However, trying to verify the above example produces a verification failure (since declarations in the class are nullable by default):
```Java
{% include_relative T_Exception2.out %}
```
One fix for this error is to require that the method always be called with a non-null argument, as the following correct class shows.
Note that the array argument `a` is specified to be non-null, so it does not need to be specified as non-null in the second signals clause.

```Java
{% include_relative T_Exception3.java %}
```

### Ordering of Clauses

Exceptional postcondition clauses can be stated in any order;
there is no meaning to one being before the other as all must be satisfied.
Consider this example in which there are two kinds of exceptions thrown.

```Java
{% include_relative T_Exception4.java %}
```

Note that if there are no `signals` clauses (and no requires clause), 
then OpenJML complains that some expected conditions cannot be proved, 
as shown in the following example.

```Java
{% include_relative T_Exception4a.java %}
```

The above gives the following output when checked with ESC.

```Java
{% include_relative T_Exception4a.out %}
```

The three verification failure messages shown above may occur in any order.
This balance between verification failures and exception specifications is an
[advanced topic](JavaErrorsAndExceptions).

### Specification in JML does not include Java Errors

In JML one does not specify behavior regarding Java Errors,
which are derived from `java.lang.Error`,
as these are mostly unrecoverable system errors like `OutOfMemoryError`
or `StackOverflowError`.

## **[Exercises](https://www.openjml.org/tutorial/exercises/SpecifyingExceptionsEx.html)**

Follow the link in the above heading to work on the exercises on this topic.
## Resources
+ [T_Exception1 file](T_Exception1.java)
+ [T_SpecifyingExceptionsNone file](T_SpecifyingExceptionsNone.java)
+ [T_Exception1a file](T_Exception1a.java)
+ [T_Exception2 file](T_Exception2.java)
+ [T_Exception3 file](T_Exception3.java)
+ [T_Exception4 file](T_Exception4.java)
+ [T_Exception4a file](T_Exception4a.java)
