---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises:
## [Arithmetic and Arithmetic Modes Tutorial](https://www.openjml.org/tutorial/ArithmeticModes)

## **Question 1**
**Given the function below determine the strongest preconditions needed to verify the function.**
```Java
{% include_relative ArithmeticExample1.java %}
```

**Learning Objectives:**
+ Understand overflow and underflow errors and how to use specifications to prevent them.

## **Question 2**
**(a) The function given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
**(b) How could you edit the code to verify the function with the original specification?**
```Java
//@ spec_public
private int playerHealth;
	
//@ requires dmg <= 0;
//@ requires 0 < playerHealth;
public int updatePlayerHealth(int dmg) {
	if(playerHealth > dmg) {
		return (playerHealth - dmg);
	}else {
		return 0;
	}
}
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
