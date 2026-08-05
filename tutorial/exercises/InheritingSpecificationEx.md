---
title: JML Tutorial - Exercises - Inheriting Specifications
---
# Inheriting Specifications Exercises:
## [Inheriting Specifications Tutorial](https://www.openjml.org/tutorial/InheritingSpecifications)

## **Question 1**
**Consider the following class, `Point`.**
```
public class Point {
    protected /*@ spec_public @*/ int x, y;

    //@ ensures x == xv && y == yv;
    public Point(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ ensures \result == x;
    //@ spec_pure
    public int getX() {
        return x;
    }

    //@ ensures \result == y;
    //@ spec_pure
    public int getY() {
        return y;
    }

    //@ assignable x;
    //@ ensures x == newX;
    public void setX(int newX) {
        x = newX;
    }

    //@ assignable y;
    //@ ensures y == newY;
    public void setY(int newY) {
        y = newY;
    }
}
```

**Now consider the following subclass, `PositivePoint`.**

```
public class PositivePoint extends Point {
    //@ public invariant 0 < x;
    //@ public invariant 0 < y;

    //@ requires 0 < xv && 0 < yv;
    //@ ensures x == xv && y == yv;
    public PositivePoint(int xv, int yv) {
        super(xv, yv);
    }
}
```

**The `PositivePoint` class restricts the `x` and `y` coordinates to be positive; note the invariants and the precondition on the constructor. This raises severeal questions:**

1. **Is `PositivePoint` a behavioral subtype of `Point` as specified?**
2. **Are the inherited implementations of the methods `setX` and `setY` correct with respect to these new invariants in `PositivePoint`?**
3. **If the inherited implementations of the methods `setX` and `setY` are not correct, what Java code would demonstrate the problem?**


## **Question 2**
**Specify an interface `NormalSetAge` that includes a new method `setAge`. The interface `NormalSetAge` must extend the interface `Age` shown in the following. The added `setAge` method should take an integer that is nonnegative, no less than the current value of `age`, and no greater than 150, and it must make the model field `age` be that number. Hint: the model field `age` will be inherited, since it is declared as an `instance` field.**

```
%{ include_relative Age.java %}
```

## **Question 3**
**Specify another interface, called `ExceptionalSetAge`, that also includes a new method `setAge` (new compared to `Age`, that is). The interface `ExceptionalSetAge` must extend the interface `Age` shown above. The added `setAge` method should take an integer that is (strictly) less than the value of `age` and leave the inherited model field `age` alone. However, so that further exercises may involve classes that extend both `NormalSetAge` and this interface (`ExceptionalSetAge`) and which can assign to additional fields, it is necessary to allow the inherited model field `age` to be assigned by the `setAge` method.  So think about what postcondition would specify the appropriate behavior.**

## **Question 4**
**Specify an interface, called `Gendered` that includes a model instance field `gender` of type `String`. Your task is to write this interface's specification and to specify a Boolean-valued `spec_pure` method named `isFemale()` that returns `true` just when the receiver (an object of a subtype of `Gendered`) is has the gender female.**

## **Question 5**
**Specify and correctly implement a class, call it `Animal` that implements the interfaces `Gendered`, `NormalSetAge`, and `ExceptionalSetAge`. You will need to implement a constructor that takes a `String` argument that determines the gender of the new object, but starts the age at 0. You may assume that animals are either male or female. Hints: think about the precondition of the constructor. Use a protected field `_gen` to represent the model field `gender` that is inherited from the (specification of the) interface `Gendered`. Note that each model field names a data group, and when a concrete field is used to represent that data group, then it must be added into that data group using an `in` annotation in JML. Being in a data group allows the representing field to be assigned when the data group is allowed to be assigned by the specification. Similarly, add a protected model field `_age` that is used to represent the inherited model field `age`. Making these concrete fields protected allows them to be inherited by subclasses of Animal. Since they are protected, the represents clauses that are used must also be protected.**

## **Question 6**
**Specify and implement a class `Human` as a subclass of `Animal`. A `Human` should have a Boolean-valued public model field `discount` that is represented by some protected concrete (instance) field. The `setAge` method should have an additional specification case that makes `discount` be `true` when the age used as an argument to `setAge` is 65 or greater. Hint: use a call to `super` in your implmenetation of `setAge`.**

**Learning Objectives:**
+ Understand what behavioral subtyping is.
+ Be able to write a represents clause to implement a model field.
+ Understand how inheritance of specification works and how new specification cases can be added to inherited specifications to make more refined behaviors.
+ Understand pitfalls of specification inheritance.

## **[Answer Key](InheritingSpecificationsExKey.md)**

## Resources
+ [Point file](https://www.openjml.org/tutorial/exercises/Point.java)
+ [PositivePoint file](https://www.openjml.org/tutorial/exercises/PositivePoint.java)
+ [Age file](Age.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
