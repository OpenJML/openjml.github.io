---
title: JML Tutorial - Calling methods in specifications (pure methods)
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

## Pure methods

The specifications we have written so far have contained just simple
expressions and operators. It is also convenient, and allowed, to call
methods in specifications --- but there are restrictions.

Expressions in specifications must not have any effect on the Java program.
Think of a program with specifications converted to run-time checks. We
can't have the checks modifiying the program that is being checked.
Similarly we can't allow static checking to have any effect on the Java program.

Thus the rule is that methods that are called in specifications must be 
_pure_, that is, must not have any side-effects. In fact JML requires that 
a method used in specifications be marked with the modifier `pure`.

Here is an example:
```
{% include_relative T_PureMethod1.java %}
```
Running OpenJML produces
```
{% include_relative T_PureMethod1.out %}
```

The call of `c.isAnythingCounted` is allowed in the specification because
it is declared `pure` in its specification. However
`c.atMax()` is not allowed because it is not declared `pure`.
If you add that modifier to the declaration of `atMax` then this example will
verify (cf. example `T_PureMethod2.java`).

Notice that these `pure` methods have no `assigns` clause. Pure methods are
not allowed to write to any fields, so if there were an `assigns` clause
it would have to be `assigns \nothing;`. In fact, for a `pure` method,
the default `assigns` clause is precisely that `assigns \nothing;`.
(For a non-pure method, the default is `assigns \everything;`.)

If you add a `pure` modifier to `count`, then OpenJML produces
```
{% include_relative T_PureMethod3.out %}
```

It is also vitally important to remember that when a method is used in a
specification, it is the _specification_ of the method that is used to 
determine its behavior, not its implementation.

This example
```
{% include_relative T_PureMethod4.java %}
```
produces this output:
```
{% include_relative T_PureMethod4.out %}
```
This `abs` function verifies successfully; however, the assertion that uses it
iin `test` does not. That is because all that the method `test` knows about the result of
`abs` is that it is greater than zero. In order to verify `test`, the 
postcondition of `abs` must be strengthened to say that if `i>0` then the
result is the same as the input. 

Methods do not always need to have precise functional specs. However, the
specification does need to be strong enough to verify whatever uses the
clients of the method need.

## Well-defined method calls

[The lesson on well-defined expressions](TBD) described how expressions in
specifications must be well-defined. For a method call, that means two things:
(a) the pre-conditions of the method must be fulfilled and (b) the method may
not throw any exceptions.

The next example shows the kind of error message that OpenJML produces when 
a mthod's precondition is not fulfilled:
```
{% include_relative T_PureMethod4.java %}
```
produces
```
{% include_relative T_PureMethod4.out %}
```
The relevant error messages include the term 'Undefined' to indicate that this
instance of an out of range index is part of a specification instead of in
Java code. Note that the `elementAt` method here verifies; it is the use of
it that is at fault.

## Termination and Exceptions

Methods marked `pure` so they can be used in specifications must satisfy two additional properties.
First they must be terminating. The specification `diverges false;` states this property for a method,
but as it is the default, it does not need to be written. See [the advanced lesson on termination](Termination)
for more on this topic.

The other property is that when a method is used in a specification it is assumed not to throw any
exceptions. It is best if the method has only `normal_behavior` specification cases,
but if it has any `exceptional_behavior` cases, they will be ignored for use in specifications.
(cf. [Multiple Behaviors](MultipleBehaviors))

## Pure constructors
You might have noticed that the constructor for `Counter` in the example
above is also marked `pure`. Constructors create new objects or arrays, so they are not allowed to be used in specifications. Nevertheless, it is helpful to 
mark a constructor as `pure` to indicate that the constructor does not modify any memory _other than setting its own fields_.

## Pure classes
A class can also be marked `pure`. This means that all the constructors and
methods of the class are themselves `pure`. This is a useful part of 
specifying an _immutable_ class, one whose objects may not be changed after
being created. Java's `String` and `Integer` are two examples of immutable classes.

