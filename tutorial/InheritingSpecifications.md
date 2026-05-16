---
title: JML Tutorial -  Inheriting Specifications
---

In classic object-oriented design, a base class, perhaps abstract, can be used without knowing what specific kind of derived class an object is at run-time.
For example, one can talk about a Shape's perimeter or area without needing
to know what kind of Shape it is.
When one writes specifications for a base class one can define its general behavior and then any derived class is expected to adhere to that behavior.
However, a derived class may also have additional and more specific behavior.
This property -- a derived class obeying the expectations of its base class -- is called *behavioral inheritance* (or _behavioral subtyping_). JML enforces it by insisting that derived classes inherit the behavior of base classes,
by inheriting their specifications.

Here is a simple example:
```
{% include_relative T_Polygon.java %}
```

In this example `T_Polygon` is an interface with a method (`sides()`) that returns a property of a polygon. Even though the method is abstract (being in an interface), 
the interface's specification states some properties:
a polygon has at least three sides.
After the interface, `Square` is a concrete class that implements `T_Polygon`.
Now the abstract `sides()` method has an implementation. In addition:
* The method `sides()` in class `Square` inherits its specification from its counterpart in `T_Polygon`
* The keyword `also` at the beginning of the specification of `sides()` in `Square` is a visual indicator that there are additional specifications in parent classes
or interfaces (much like the annotation `@Override` does in Java).
* Due to inheritance of specifications, the method `sides()` in `Square` is specified by two *behaviors* (in the sense of the discussion in the [lesson on multiple behaviors](MultipleBehaviors)), and it must satisfy each of its behaviors. (Thus it is best that these two specifications not contradict each other.)
* The instance methods in `T_Polygon` have no implementation
(because they are abstract methods of an interface),
so there is no body to verify.
However, due to specification inheritance, their specifications will be verified when verifying the implementing methods of a derived class,
as is done with `sides()`.

When the methods of `T_Polygon` are called in some client class, the client class only knows the properties based on the (static) type of the reference it has.
For example, when the client only has a reference to an object of static type `T_Polygon`, then it only knows about the specification of `T_Polygon` as a way to reason about that object's behavior. Therefore, verifying the following test:
```
{% include_relative T_PolyTest.java %}
```
produces
```
{% include_relative T_PolyTest.out %}
```

In `test()`, only the properties of a `T_Polygon` are known; after all, any kind of `T_Polygon` instance might have been passed in as an argument.
But in `test2()`, we know the argument (`sq`) is a `Square`,
so the assertions pass.

We can also check the type of the input `T_Polygon` with a Java statement. If openjml knows that the argument is a `Square` then openjml can prove the more specific properties. So, the following version verifies:
```
{% include_relative T_PolyTest2.java %}
```

This simple example is intended only to show specification inheritance. The next two lessons
on specification with [model fields](ModelFields) and [model methods](ModelMethods), show more complex examples that specify abstract classes.
