---
title: JML Tutorial -  Inheriting Specifications
---

In classic object-oriented design, a base class, perhaps abstract, can be used without knowing what specific kind of derived class an object is at run-time.
For example, one can talk about a Shape's perimeter or area without needing
to know what kind of Shape it is.
When one writes specifications for a base class one can define its general behavior and then any derived class is expected to adhere to that behavior.
However, a derived class may have additional and more specific behavior.
This property -- a derived class obeying the expectations of its base class -- is called *behavioral inheritance*. JML enforces it by insisting that derived classes inherit the behavior of base classes,
by inheriting their specifications.

Here is a simple example:
```
{% include_relative T_Polygon.java %}
```

In this example `T_Polygon` is an interface with a method (`sides()`) that returns a property of a polygon. Even though the method is abstract (being in an interface), 
the interface's specification states some properties:
a polygon has at least three sides.`
Following this, `Square` is a concrete class that implements the interface `T_Polygon`.
Now those abstract methods have an implementation. For example:
* The method `sides()` in class `Square` inherits its specification from its counterpart in `T_Polygon`
* The keyword `also` at the beginning of the specification of `sides()` in `Square` is a visual indicator that there are additional specifications in parent classes
or interfaces (much like the annotation `@Override` does in Java).
* The method `sides()` in `Square` ends up with two *behaviors* (in the sense of the discussion in the [lesson on multiple behaviors](MultipleBehaviors)).
* The method `sides()` in `Square` must satisfy each of its behaviors independently, so they should not contradict each other
* Any methods in `T_Polygon` have no implementation (because they are abstract methods of an interface), so there is nothing to verify about them.
However their specifications will be checked when verifying any derived class, as is done with `sides()`.

When the methods of `T_Polygon` are called in some client class, the client class knows the properties based on the (static) type of the reference it has.
For example,
```
{% include_relative T_PolyTest.java %}
```
produces
```
{% include_relative T_PolyTest.out %}
```

In `test()`, only the properties of a `T_Polygon` are known; after all, any kind of `T_Polygon` instance might have been passed in.
But in `test2()`, we know it is a `Square`, so the assertions pass now.

We can also check the type of the input `T_Polygon`. If we know it is a `Square` then we can prove the more specific properties.
This version verifies fine:
```
{% include_relative T_PolyTest2.java %}
```

This simple example is intended only to show specification inheritance. The next two lessons
on specification with [model fields](ModelFields) and [model methods](ModelMethods), show more complex examples that specify abstract classes.
