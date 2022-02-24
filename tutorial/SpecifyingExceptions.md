----------
title: Specifying Exceptions
----------

# Specifying behavior with exceptions

JML can specify exception execution paths just as well as normal execution paths.
A normal execution has associated postconditions --- `ensures` clauses. The logic is --- if the method exits normally, then the postcondition must be true.
Similarly exits with exceptions use an exceptional postcontiion --- `signals` clauses.
A `signals` clause has this syntax: `signals (E e) <expression>`
where `E` is some exception type (derived from or the same as `java.lang.Exception`).
The meaning of this clause is --- if the method terminates with an exception derived from `E`, then the given expression must be true.
[ JML does not specify behavior regarding Java Errors as these are mostly unrecoverable system errors like OutOfMemoryError or StackOverflowError.]

So we could write this trivial example:
```
```
which verifies successfully. Note that the specification includes a second kind of clause, the `signals_only` clause.
This clause lists the kinds of exceptions that are expected to be thrown from the method. 
JML requires the specification to list `RuntimeException` even though Java does not require declaring `RuntimeException` in a throws clause
in order to make it explicitly clear what exceptions might be thrown.

If we omit any exceptions, by saying `signals_only \nothing`, a verification failure results.
```
// openjml --esc T_Exception1a.java
//@ nullable_by_default
public class T_Exception1a {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (NullPointerException e) v == null;
    public int value(V v) {
        return v.value;
    }
}

   
```
```
T_Exception1a.java:13: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method value
        return v.value;
                ^
1 verification failure
```

The `signals_only` specification comes explicitly into play when the program wants to throw an exception. Consider
```
// openjml --esc T_Exception1b.java
//@ nullable_by_default
public class T_Exception1b {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (NullPointerException e) v == null;
    //@ signals_only \nothing;
    public int value(V v) {
        if (v == null) throw new NullPointerException();
        return v.value;
    }
}

   
```
It produces the output
```
T_Exception1b.java:14: verify: The prover cannot establish an assertion (ExceptionList: T_Exception1b.java:12:) in method value
        if (v == null) throw new NullPointerException();
                       ^
T_Exception1b.java:12: verify: Associated declaration: T_Exception1b.java:14:
    //@ signals_only \nothing;
        ^
2 verification failures
```
Here the method explictly throws an exception, but as that exception is not specified to be thrown, OpenJML complains.


In order to say that an exception is never thrown, use a `signals` clause with a `false` predicate.
Then the `signals` clause means --- if an exception is thrown then `false` --- which is equivalent to saying
"if true, then an exception may not be thrown", or equivalentlyr, "an exception may not be thrown".

Here is an example:
```
// openjml --esc T_Exception2.java
//@ nullable_by_default
public class T_Exception2 {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (Exception e) false;
    public int value(V v) {
        return v.value;
    }
}

   
```
But trying to verify this example produces a verification failure:
```
```
as it should. We can guard against an exception by requiring that the method always be called with a non-null argument:
```
// openjml --esc T_Exception3.java
//@ nullable_by_default
public class T_Exception3 {

    public static class V {
        public int value;
    }

    //@ requires v != null;
    //@ ensures \result == v.value;
    //@ signals (Exception e) false;
    public int value(V v) {
        return v.value;
    }
}

   
```
which now verifies again.
