---
title: JML Tutorial - Model Fields and Datagroups
---

When writing specifications for an abstract parent class or interface and a concrete derived class, the parent class needs to express its properties
in terms of some abstract quantities. _Model fields_ can be used to describe the properties of an abstract class and _datagroups_ are used as an
abstraction of frame conditions.

## Using model fields

Model fields:
* Model fields are specification-only fields that encapsulate some property of a class (typically, but not necessarily, an abstract class or interface).
* The model field can be used in the specification of the abstract class.
* A model field is given an implementation by writing a `represents` clause in the derived class; this connects the model field to the concrete implementation.
* A model field can also be used within a concrete class to represent some characteristic that is not explicitly present in the concrete class.
* A model field is typically an _instance_ field. Java only allows static fields in an interface. But in JML one can declare instance model fields
in an interface (or class) using the modifier `instance`. As the (Java) default is `static` for field declarations, the `instance` keyword is required in this case.

Datagroups:
* A model field is also a _datagroup_; or a standalone datagroup (not associated with an abstract value) can be declared using the type `JMLDataGroup`.
* A datagroup is an abstraction of a frame condition. 
   * In the abstract class the datagroup can be used in a frame condition
   * In the concrete class specific fields can be declared to be _in_ that datagroup

Here is a working example that verifies, with commentary below.
```
{% include_relative Polygon.java %}
```

* `Polygon`is an (abstract) interface with a concrete implementation `Square`
* `Polygon` declares two properties, as model fields: `sides` (the number of sides) and `longestSide` (the length of the longest side of the polygon)
* There is an invariant limiting the length of the sides and another one saying that all polygons have at least 3 sides.
* There are two simple methods that return the values of `sides` and `longestSide`. These are pure (do not change anything).
* The method `twice` doubles the size of the polygon. 
  * It has a precondition so that the resulting polygon still satisfies the invariant.
  * It has an `assigns` clause saying what is modified. 
  * It has a postcondition saying what happens to the memory locations that are modified.

`Square` is an implementation of `Polygon`:
* `Square` has just one data member, `side` (the length of a side of the square)
* The constructor for `Square` initializes `side`; it needs a precondition in order to satisfy the invariant for `Polygon`, which applies to `Square` by inheritance.
* The clause `represents sides = 4` gives a value to the `sides` model field in `Polygon`
* The clause `represents longestSide = side` gives a value to the `longestSide` model field 
* And the `side` field is declared to be in `longestSide` . When `twice` (abstractly) assigns to the model field `longestField`, then all the fields
that are _in_ `longestField` are considered assigned to.
* Then all the methods that `Square` inherits from `Polygon` are implemented as expected, but they can inherit all their specifications from `Polygon`. 
No additional specifications are needed. Look at `sides()` as an example: the specification says it returns the value of `sides`, which is given a value
by the represents clause, so the implementation of `Square.sides()` satisfies the abstract specification given for `Polygon.sides()`.

`Test` just checks that the specifications given for `Polygon` work to verify some simple uses of the interface and its specifications.
* Note that the implementation and verification of `Test.test()` only use `Polygon` and its specifications.
* The `assert` in `test2` fails because a polygon (as implemented) can have a variety of numbers of sides.
* But the `assert` in `test3` succeeds, because a `Square` knows how many sides it has.
* In `test4()` we do a type test to see if the input `polygon` is a `Square`, and if so, we know how many sides it has.

The output when verifying the example above (though you may want to add the `--progress` option) is this:
```
{% include_relative Polygon.out %}
```

## Using datagroups

In the above example, `longestSide` does not quite properly capture the effect of `twice()`, which alters the lengths of all of the sides, not just
the longest one. The following code separates the datagroup aspect of `longestSide` into a more general, standalone, datagroup named `allSides`.
This code is only slightly different than the previous listing. In particular, `Square` and `Test` are precisely the same. But now an implementation of
another derived class, `Triangle` (with three different sides) is clearer: put all three sides `in` `allSides` and make the implementation of 
`longestSide` be the maximum of the three sides.

```
{% include_relative Polygon2.java %}
```
