---
title: JML Tutorial - Exercises - Frame Conditions 
---
# Frame Conditions Exercises:
## [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions)

## **Question 1**
**The class `FrameCondEx1` puts in `maxValue` the maximum of the fields `x` and `y`. However, the code is unable to be verified; determine what specifications are needed to verify the program.**
```Java
{% include_relative FrameCondEx1.java %}
```

## **Question 2**
**The following class does not verify. What frame conditions and code changes need to be made so that it will verify? (Note that the `equals` method must remain `spec_pure` if it is to be used in other specifications, and that the `equals` method does _not_ override the `Object`'s method because it has a different argument type.)**
```Java
{% include_relative Money.java %}
```

**Learning Objectives:**
+ Gain more experience writing frame conditions and using the `assignable` clause
+ Understand how to use `\old` in JML expressions
+ Understand the importance of denoting when memory locations have been modified

## Resources
+ [Question 1 Java](FrameCondEx1.java)
+ [Question 2 Java](Money.java)

## **[Answer Key](FrameCondExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**


