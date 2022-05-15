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
%include T_Exception1.java
```
which verifies successfully. Note that the specification includes a second kind of clause, the `signals_only` clause.
This clause specifies the kinds of exceptions that may be thrown from the method. 
JML requires the specification to list `RuntimeException` even though Java does not require declaring `RuntimeException` in a throws clause
in order to make it explicitly clear what exceptions might be thrown.

If we omit any exceptions, by saying `signals_only \nothing`, a verification failure results.
```
%include T_Exception1a.java
```
```
%include T_Exception1a.out
```

The `signals_only` specification comes explicitly into play when the program wants to throw an exception. Consider
```
%include T_Exception1b.java
```
It produces the output
```
%include T_Exception1b.out
```
Here the method explictly throws an exception, but as that exception is not specified to be thrown, OpenJML complains.


In order to say that an exception is never thrown, use a `signals` clause with a `false` predicate.
Then the `signals` clause means --- if an exception is thrown then `false` --- which is equivalent to saying
"if true, then an exception may not be thrown", or equivalently, "an exception may not be thrown".

Here is an example:
```
%include T_Exception2.java
```
But trying to verify this example produces a verification failure:
```
%include T_Exception2.out
```
as it should. We can guard against an exception by requiring that the method always be called with a non-null argument:
```
%include T_Exception3.java
```
which now verifies again.


LAST_MODIFIED
