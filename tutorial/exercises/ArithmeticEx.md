---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises:
## [Arithmetic and Arithmetic Modes Tutorial](https://www.openjml.org/tutorial/ArithmeticModes)

## **Question 1**
**Given the method below determine the strongest preconditions needed to verify it.**
```Java
{% include_relative ArithmeticExample1.java %}
```

**Learning Objectives:**
+ Understand overflow and underflow errors and how to use specifications to prevent them.

## **Question 2**
**(a) The method given below cannot be verified; write an assume statement (or several assume statements) in the code, without changing the Java code, to allow it to be verified.**

**(b) How could you edit the code to allow the method to verify without adding any specifications?**

```Java
{% include_relative ArithmeticExample2.java %}
```
**Learning Objectives:**
+ Gain more experience with handling overflow 
+ Understand how to write specifications that reflect the requirements and outputs wanted  

## **[Answer Key](ArithmeticExKey.md)**

## **Resources:**
+ [Arithmetic Exercises](ArithmeticEx.md)
+ [Question 1 Java](ArithmeticExample1.java)
+ [Question 2 Java](ArithmeticExample2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
