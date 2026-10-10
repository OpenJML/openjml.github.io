---
title: JML Tutorial - Specifying Constructors
---

Constructors are a special kind of method and also need to be specified. The syntax and concepts for doing so are very similar to method specifications, with just a few extra rules.

A simple class with a few data fields might have constructors that look like this:
```
{% include_relative T_constructors1.java %}
```

The first constructor simply initializes the fields from the constructor's argument list. The specification for the constructor first requires that the 
input values are non-negative and then simply says that after the constructor is finished, the newly constructed object's data fields equal the input
values. The heading `normal_behavior` says that the constructor does not throw any exceptions; it is discussed further [here](MultipleBehaviors#SpecializedBehaviors).
There is also the modifier `pure`; more on that below.

The second constructor is similar to the first. The specification is perhaps less obvious because of the constructor call (the `this` call) of the first
constructor. The second constructor uses the _specification_ of the first constructor to prove that its implementation---which is just the this-call--- satisfies its specification.

Both of these specifications are readily verified.

## Framing

Specifying frame conditions for constructors is similar to specifying frame conditions for method specifications, although a constructor is always allowed to assign to the object being constructed. As with methods, the default frame condition is `assignable \everything`.  On the other hand, a frame condition of `assignable \nothing` means that only the fields of the object being constructed may be assigned by the constructor; in particular, no static fields of the class may be assigned when the constructor is `pure`.  See [the lesson on frame conditions](FrameConditions) for more about this subject; however, note that a constructor may not be specified as `spec_pure`, because the only way to call a constructor is with Java's `new` operator, which necessarily constructs an object on the heap.

The following example shows that if there is a static field that a constructor should assign, then the constructor cannot be pure and would need an assignable clause:

```
{% include_relative T_constructors2.java %}
``` 

This specification is also readily verified, though it needs the precondition to be sure that we don't overflow the `count` field; see [the lesson on artithmetic](ArithmeticModes) for more about this topic.

The implementation of these constructors is so simple, and common, that one might think that inferring the specification from the implementation should be easy. Indeed such specification inference is a not-yet-implemented goal that would reduce some of the specification-writing burden.

TODO- say more about the whole initialization process and initializer specs.

## **[Exercises](https://www.openjml.org/tutorial/exercises/SpecifyingConstructorsEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_constructors1 file](T_constructors1.java)
+ [T_constructors2 file](T_constructors2.java)
