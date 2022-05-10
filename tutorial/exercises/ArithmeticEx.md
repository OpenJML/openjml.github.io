---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises:
## **Question 1**
**Given the function below determine the strongest preconditions needed to verify the function.**
```Java
public class ArithmeticExample1 {
	//@ spec_public
	private int sum;

	//@ ensures 0 < sum < Integer.MAX_VALUE;
	public void sumThreeNums(int n1, int n2, int n3) {
		sum = n1 + n2 + n3;
	}	
}
```
**Learning Objectives:**
+ Understand overflow and underflow errors
+ Understand `Integer.MAX_VALUE`
+ Gain more experience writing preconditions
+ Gain more experience with the `assigns` clause

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
