---
title: JML Tutorial - Exercises - Verifying Method Calls
---
# Verifying Method Calls Exercises:
## **Question 1**
**Write two functions that perform the following: an function that adds two integer arrays and a function that returns true if the arrays to be added are of the same size. Use the following function headers to help you. Determine the specifications needed to verify your functions.**
```Java
public int[] addArrays(int[] a, int[] b);

public boolean sameSize(int[] a, int[] b);
```
**Learning Objectives:**
+ Understand how to verify method calls
+ Gain more experience writing JML specifications 

## **Question 2**
**The program below is checking whether the user has enough material for an area given the dimensions of the area and the amount of material the user has. However, the program is unable to be verified; determine where in the specifications it is failing, and fix it.**
```Java
//@ ensures \result <==> (area(w, h) > materialSqFt);
public boolean enoughMaterial(int materialSqFt, int w, int h) {
	int area = area(w, h);
		
	return (area > materialSqFt);	
}
	
//@ ensures \result > 0;
//@ ensures \result >= w;
//@ ensures \result >= h;
//@ pure
public int area(int w, int h) {
	int A = w*h;

	return A;	
}
```
**Learning Objectives:**
+ Understand the importance of verifying method calls
+ Understand the importance of `assume` and `assert` statements for verifying method calls
+ Gain more experience with the process of verifying method calls

## **[Answer Key](VerifyingMethodCallsExKey.md)**
