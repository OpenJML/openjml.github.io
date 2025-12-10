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

Thus the rule is that methods that are called in specifications must not
have any effect on the Java program state at the beginning of the method call (the _pre-state_).
Such methods are called _pure_.

Methods called in specifications must also be deterministic. Thus they may not depend on random events or on
external properties (such as the system clock or environmental variables or system Properties) that may change during the execution of
the program.

There is a hierarchy of four kinds of purity, all of which share the
property of no effect on the initial Java program state.

**pure** methods: This basic kind of `pure` method has no side effects on the external program
state but may allocate and dispose of objects within the method and may return
a newly allocated object (e.g. a `String`). Because it can return a fresh object,
it is not a deterministic method from the point of view of the Java program heap.

**spec_pure** methods: A `spec_pure` method is a `pure` method that does not return any
fresh object; it either returns a primitive value or an object reference that was
already allocated in the pre-state. Consequently it is deterministic. 
A method must be at least `spec_pure` to be used in a specification.

**strictly_pure** methods: A `strictly_pure` method is a `spec_pure` method that does not
allocate any new objects in the body of the method. Such a method has no effect on the 
object heap at all; it may read heap values and perform computations on the method's
local stack. Though a `strictly_pure` method is generally indistinguishable by a calling method from a 
`spec_pure` method, some tools can benefit by knowing that a method makes no changes,
even internally, to the program heap.

**no_state** methods: A `no_state` method is one that does not depend on the program heap
at all. Hence such a method (if deterministic) returns the same value for the same arguments
no matter in what heap or program state it is invoked. Examples are purely mathematical
library functions.

A method marked with any kind of purity should not have any `assignable` clauses;
all the method's behaviors are implicitly `assignable \nothing`.
Any `assignable` clause that is present must be `assignable \nothing`.

To be called in a method specification, a method must be at least `spec_pure`.
For historical reasons, a method parked `pure` that returns a primitive value
is implicltly `spec_pure` and may be used in a specification. But it is
better style to just mark such methods as `spec_pure`.

Similarly, if a method is truly independent of the heap, it is good style to 
mark it as `no_state`. Doing so simplifies reasoning about uses of the method.

Here is an example:
```
{% include_relative T_PureMethod1.java %}
```
Running OpenJML produces
```
{% include_relative T_PureMethod1.out %}
```

The call of `c.isAnythingCounted` is allowed in the specification because
it is declared `spec_pure` in its specification. However
`c.atMax()` is not allowed because it is not declared `spec_pure`.
If you add that modifier to the declaration of `atMax` then this example will
verify (cf. example `T_PureMethod2.java`).

Notice that these `pure` methods have no `assigns` clause. Pure methods are
not allowed to write to any fields, so if there were an `assigns` clause
it would have to be `assigns \nothing;`. In fact, for a `pure` method,
the default `assigns` clause is precisely that `assigns \nothing;`.
(For a non-pure method, the default is `assigns \everything;`.)

If you add a `pure` modifier to `count` (as in `T_PureMethod3.java`), then OpenJML produces
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
in `test` does not. That is because all that the method `test` knows about the result of
`abs` is that it is greater than zero. In order to verify `test`, the 
postcondition of `abs` must be strengthened to say that if `i>0` then the
result is the same as the input. 

Methods do not always need to have precise functional specs. However, the
specification does need to be strong enough to verify whatever uses the
clients of the method need.

## Well-defined method calls

[The lesson on well-defined expressions](WellDefinedExpressions) described how expressions in
specifications must be well-defined. For a method call within a specification clause, that means two things:
(a) the pre-conditions of the method must be fulfilled and (b) the method may
not throw any exceptions.

The next example shows the kind of error message that OpenJML produces when 
a method's precondition is not fulfilled:
```
{% include_relative T_PureMethod5.java %}
```
produces
```
{% include_relative T_PureMethod5.out %}
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
above is also marked `spec_pure`. Constructors create new objects or arrays, so they are not allowed to be used in specifications. Nevertheless, it is helpful to 
mark a constructor as `ispec_pure` to indicate that the constructor does not modify any memory _other than setting its own fields_.

## Pure classes
A class can also be marked `pure`. This means that all the constructors and
methods of the class are themselves `pure`. This is a useful part of 
specifying an _immutable_ class, one whose objects may not be changed after
being created. Java's `String` and `Integer` are two examples of immutable classes.

## **[Using Method Calls in Specifications Problem Set](https://www.openjml.org/tutorial/exercises/CallingMethodsEx.html)**
