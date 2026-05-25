---
title: JML Tutorial - Exercises - Postconditions
---
# Postcondition Exercises:
## [Postconditions Tutorial](https://www.openjml.org/tutorial/Postconditions)

## **Question 1**
**(a) Suppose that we want to change the precondition of the method `multiplyByTwo` below so that the argument (`num`) only has to be (strictly) greater than -1, that is the precondition would be `-1 < num < 100.
Why would this cause a verification error with the existing code?**

```Java
//@ requires 0 < num < 100;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```

**(b) How you could fix the postcondition so that the existing code would verify with the precondition `-1 < num < 100`? Note that you are to only change the postcondition, not the code in the body of the method and you are to use the new precondition `-1 < num < 100`.**

**(c) Suppose we revert to the original specifications where the precondition is that `0 < num`. The function is unable to be verified. Determine where in the specifications it is failing, and fix it by (only) changing the specification.**

**(c) Suppose the code was updated to the following, with the original precondition that `0 < num`. What is the strongest postcondition that will allow the code in the body below to be verified?**
```Java
public int divideByTwo(int num) {
       return num/2;
}
```

## **Question 2**
** (a) Given a rectangle of width w and height h, write a Java method that finds the area of the rectangle and returns it. (b) What is the strongest specifications that verifies the code you wrote?
The function header is given below.**
```Java 
public int area(int w, int h);
```

## **Question 3**
**Specify and correctly implement a method that takes a sorted integer array, and an element and uses a binary search to check whether the element occurs in the array (and returns _true_ when it occurs in the array and _false_ otherwise).**

**Learning Objectives:** 
+ Gain more experience writhing pre and postconditions 
+ Understand the importance of postconditions and how they can be used to get the correct output for a program

## **[Answer Key](PostCondExKey.md)**

