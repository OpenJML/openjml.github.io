---
title: JML Tutorial - Exercises - Verifying Method Calls
---
# Verifying Method Calls Exercises Key:
## [Verifying Method Calls Tutorial](https://www.openjml.org/tutorial/MethodCalls)

## **Question 1**
**Answer and Explanation:**
One solution that verifies as correct is the following.
```Java
{% include_relative MethodCallsEx1.java %}
```

If one uses the standard computation for the average `(x+y)/2`, then it is important to avoid wrap-around of the Java integers used by making sure that the arguments `x` and `y` can be added together without such problems. This is the reason for the preconditions that say both arguments must be positive integers that their sum is no more than `Integer.MAX_VALUE`. Another possibility would be to require that both arguments are less than `Integer.MAX_VALUE/2`.

The `isNonNegative` function has a straightforward postcondition. However, it is necessary to specify that it is `pure`, so that it does not have side effects when called.

## **Question 2**
**Answer and Explanation:**
When one uses OpenJML's ESC on the program, one sees that all the problems lie in the areaOfRectangle method. There are several problems:

1. The multiplication `w*h` may overflow,
because the result may be too large to fit in an `int`.
2. The result (`A`) may not equal the mathematical result, since the specification uses mathematical integers and the result may not fit into an `int` or may wrap around to a negative number.
3. Because the result may be negative when put into an `int` result, the result may no longer satisfy `0 < w <= \result` violating two postconditions of `areaOfRectangle`

Fixing these problems can be done by adding preconditions on `w` and `h` in `areaOfRectangle`, in particular the requirement that both `w` and `h` are positive (`0 < w && 0 < h`, so that the result of the multiplication will be mathematically positive) and a precondition that the product `w*h` fits into an `int` (`w*h <= Integer.MAX_VALUE`).
 
```Java
{% include_relative MethodCallsEx2.java %}
```

However, when one adds these preconditions to `areaOfRectangle` then the call to that method in `enoughMaterial` may no longer satisfy `areaOfRectangle`'s precondition, so to get the program to verify, it is necessary to add a precondition to `enoughMaterial` to constrain the values of `w` and `h` (this is the first precondition of `enoughMaterial` above).

## **Resources:**
+ [Verifying Method Calls Exercises](VerifyingMethodCallsEx.md)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
