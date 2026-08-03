---
title: JML Tutorial - Exercises - Inheriting Specifications
---
# Inheriting Specifications Exercises:
## [Inheriting Specifications Tutorial](https://www.openjml.org/tutorial/InheritingSpecifications)

## **Question 1**
**Specify an interface `NormalSetAge` that includes a new method `setAge`. The interface `NormalSetAge` must extend the interafce `Age` shown in the folowing. The added `setAge` method should take an integer that is nonnegative, no less than the current value of `age`, and no greater than 150, and it must make the model field `age` be that number. Hint: the model field `age` will be inherited, since it is declared as an `instance` field.**

```
%{ include_relative Age.java %}
```

## **Question 2**
**Specify another interface, called `ExceptionalSetAge`, that also includes a new method `setAge` (new compared to `Age`, that is). The interface `ExceptionalSetAge` must extend the interafce `Age` shown above. The added `setAge` method should take an integer that is (strictly) less than the value of `age` and leave the inherited model field `age` alone. However, so that further exercises may involve classes that extend both `NormalSetAge` and this interface (`ExceptionalSetAge`) and which can assign to additional fields, it is necessary to allow the inherited model field `age` to be assigned by the `setAge` method.  So think about what postcondition would specify the appropriate behavior.**


**Learning Objectives:**
+ Understand what behavioral subtyping is.
+ Understand how inheritance of specification works.
+ Understand pitfalls of specification inheriance.

## **[Answer Key](InheritingSpecificationsExKey.md)**

## Resources
+ [Age file](Age.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
