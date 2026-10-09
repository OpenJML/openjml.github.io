---
title: JML Tutorial - Exercises - Invariant clauses
---
# Exercises
## [Invariants Tutorial](https://www.openjml.org/tutorial/Invariants)

## **Question 1**
**The following class does not verify. Add one or more `invariant` clauses and fix the specifications and the code so that it verifies and makes the assertions in method `test()` pass.** 

```Java
{% include_relative ScreenPoint.java %}
```

In your solution, you must add one or more `invariant` clauses to the class. Doing that may make it necessary to change some method preconditions. However, changing those preconditions will also require changes in the code for the method `test()`, but you should make those without changing the calls to `moveRight` and `moveUp` and the assertions that follow those calls.

## **Question 2**
**Consider the following class that also does not verify. Write one or more `invariant` clauses and an `assume` statement to explain (to OpenJML) why the code in the `equals` method is correct.**

```Java
{% include_relative Rational.java %}
```

Note that the `equals` method above does not override `Object`'s `equals` method, as it has a different type of argument.

## **[Answer Key](InvariantsExKey)**

## Resources
+ [Question 1 Java](ScreenPoint.java)
+ [Question 2 Java](Rational.java)
+ [All exercises](exercises)
