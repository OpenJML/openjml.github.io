---
title: JML Tutorial - Assert statements (assert and check)
---
A JML *assert* statement states a condition that is expected to hold at a point
within the body of a method. Such statements are not part of a method's interface 
specification, but they can help (either staticly with ESC or at runtime with RAC)  debug the execution of a method
or, sometimes, provide a lemma that aids in the verification of the method body.

An assert statement is simple: in a JML comment, it is just the **assert**
keyword followed by a predicate and terminated with a semicolon, as in 
the following example.

```
{% include_relative T_assert1.java %}
```

The above example verifies with OpenJML, but the following variation does not:

```
{% include_relative T_assert2.java %}
```

produces

```
{% include_relative T_assert2.out %}
```

because if `i` is 0, then `neg` is 0 and the assert fails.
In this second example, which is at fault: the code or the assert statement?
Well, that depends on what the intent of the method is: should `neg` be a 
negative number or a non-positive number? The verifier can only identify
the discrepancy between the code and the specification, giving the 
software writer the opportunity to consider the problem and make an
appropriate correction.

Java has its own `assert` statement. By default, the Java assert 
statements are ignored at runtime, unless explicitly enabled.
When enabled (cf. the Java `-ea` or `-esa` runtime option) a Java program will
throw an `AssertionError` if the predicate in the Java assert statement
is false.

OpenJML will interpret a Java `assert` statement in the same way that it
does a JML `assert` statement; it issues a verification error if it 
cannot prove the designated predicate true. So this example, like the 
example above,

```
{% include_relative T_assert3.java %}
```

produces similar output:

```
{% include_relative T_assert3.out %}
```

## Check statement

The `check` statement (e.g. `check neg < 0;`) is similar to the `assert` statement.
It also effects a test of whether the given predicate is always true.
However, the two statements differ in their effect on the subsequent logic
of the program:

* A `check` statement tests the predicate but makes no assumption about whether the
predicate is subsequently true or false. A `check` statement essentially says,
please just check whether the given predicate is true or false.
* An `assert` predicate tests the predicate and then _assumes that it is subsequently true_.
An `assert` statement essentially says, this predicate is supposed to be true, so pleasae test it
and assume it to be true for analyzing subsequent code.

For example,

```
{% include_relative T_assert4.java %}
```

produces this output:

```
{% include_relative T_assert4.out %}
```

This explanation points to a potentially confusing point about `assert` statements. If
the given predicate is always false, then the implicit assumption, after the assert check,
that it is true causes a complete halt to the symbolic execution -- there is no pre-state
that satisfies the assert/assume combination. A `check` would be better to be used in such cases.


## **[Assert Statements Problem Set](https://www.openjml.org/tutorial/exercises/AssertEx.html)**
