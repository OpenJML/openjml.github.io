---
title: JML Tutorial - Exercises - Verifying Method Calls
---
# Verifying Method Calls Exercises:
## [Verifying Method Calls Tutorial](https://www.openjml.org/tutorial/MethodCalls)

## **Question 1**
**Write two methods that do the following: `averageMeasures` averages two integers (returning a result that is accurate to within 9 decimal places), assuming both arguments are non-negative, and `isNonNegative`, which returns true just when its integer argument is non-negative. The first method must call the second. Use the following headers for these methods and write the method specifications needed to verify your implementations.**
```Java
public double averageMeasures(int x, int y);

public boolean isNonNegative(int i);
```

## **Question 2**
**The `enoughMaterial` method below is checking whether the user has enough material for an area given the dimensions of the area (`w` and `h`) and the amount of material the user has (`materialSqFt`). However, the program is unable to be verified; determine the cause of the verification failure and fix it by changing only the specifications of the two methods, without changing the code of either method.**
```Java
    //@ requires 0 < materialSqFt;
    //@ ensures \result <==> (areaOfRectangle(w,h) < materialSqFt);
    public boolean enoughMaterial(int materialSqFt, int w, int h) {
        int area = areaOfRectangle(w, h);
        return (area < materialSqFt);	
    }

    //@ ensures 0 < \result;
    //@ ensures w <= \result;
    //@ ensures h <= \result;
    //@ ensures \result == w*h;
    //@ spec_pure
    public int areaOfRectangle(int w, int h) {
        int A = w*h;
        return A;
    }	
```
**Learning Objectives:**
+ Understand the importance of verifying method calls
+ Gain more experience with the process of specifying and verifying methods, especially those whose implementations involve method calls

## **[Answer Key](MethodCallsExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
