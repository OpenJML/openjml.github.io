---
title: JML Tutorial - Exercises - Postconditions
---
# Postcondition Exercises:
## [Postconditions Tutorial](https://www.openjml.org/tutorial/Postconditions)

## **Question 1**
**(a) Suppose that we want to make the precondition of the method `multiplyByTwo` below be such that the argument (`num`) only has to be (strictly) greater than -1, that is the precondition would be changed to `-1 < num < 100.
Why would this cause a verification error (with the code in the body)?**

```Java
    //@ requires -1 < num < 100;
    //@ ensures num < \result;
    public int multiplyByTwo(int num) {
        return num*2;    // ERROR: may not satisfy postcondition!
    }
```

**(b) How you could fix the postcondition above so that the existing code would verify with the new precondition `-1 < num < 100`? Note that you are to only change the postcondition, not the code in the body of the method and you are to use the new precondition `-1 < num < 100`.**

## **Question 2**

**Consider the following code. What is the strongest postcondition[^1] that will allow the code in the body to be verified?**
```Java
public int divideByTwo(int num) {
       return num/2;
}
```

## **Question 3**
**Given a rectangle of width w and height h: (a) write a Java method that finds the area of the rectangle and returns it. (b) What is the strongest specifications that verifies the code you wrote?
The function header is given below.**
```Java 
public int area(int w, int h);
```

## **Question 4**
**Specify and correctly implement a method that returns the average of two `double`s. The interface of the method should be as follows.**

```
    public double average(double x, double y);
```

**Learning Objectives:** 
+ Gain more experience writhing pre and postconditions 
+ Understand the importance of postconditions and how they can be used to get the correct output for a program

## **[Answer Key](PostCondExKey.md)**

## Resources
+ [Java code for question 1](PostCondEx1a.java)
+ [Java code for question 2](PostCondEx2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises) 

## Footnotes
[^1]: For more about the strength of predicates, see the [preconditions tutorial](https://www.openjml.org/tutorial/Preconditions#strength-of-predicates-and-specifications).
