---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises:
## [Assert Statements Tutorial](https://www.openjml.org/tutorial/AssertStatement)

## **Question 1**
**Given the code below, write the strongest[^1] assert statements at the places indicated to verify the method `max3` in the class below.**

```Java
{% include_relative AssertExample1.java %}
```

**Learning Objectives:** 
+ Gain practice using `assert` statements
+ Understand how `assert` can be used

## **Question 2**
**Given the method below, write the strongest[^1] assert statements that will verify at the places indicated.**

```Java
{% include_relative AssertExample2.java %}
```
**Learning Objectives:** 
+ Gain more experience writing `assert` statements

## **[Answer Key](AssertExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Java code for question 1](AssertExample1.java)
+ [Java code for question 2](AssertExample2.java)

## Footnotes

[^1]: An assert statement `assert P;` is stronger than assert statement `assert Q;` when the predicate `P` is stronger than the predicate `Q` (that is, when `P` implies `Q`). See [the tutorial section on preconditions](https://www.openjml.org/tutorial/Preconditions.html) for more about the strength of predicates.
