---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises Key:
## [Arithmetic Tutorial](https://www.openjml.org/tutorial/ArithmeticModes)

## **Question 1**
One way to avoid the potential underflows and overflows in Java's computation is by adding the assumptions shown in the following.

```Java
public class ArithmeticExample1 {
	
	private int sum;

	public void sumThreeNums(int n1, int n2, int n3) {
            //@ assume Integer.MIN_VALUE <= n1 + n2 <= Integer.MAX_VALUE;
            //@ assume Integer.MIN_VALUE <= n2 + n3 <= Integer.MAX_VALUE;
            //@ assume 0 <= n1 + n2 + n3 <= Integer.MAX_VALUE;
            sum = n1 + n2 + n3;
            //@ assert 0 <= sum <= Integer.MAX_VALUE;	
	}
	
}
```

The first two assumptions added above the assignment to `sum` make sure that intermediate computations will not overflow or underflow, while the third assumption makes sure that the entire computation (`n1 + n2 + n3`) will not overflow or underflow in `int` arithmetic. All these assumptions seem necessary (and all could be made into [preconditions](Preconditions) for the method.

One could write a more constructive set of assumptions, but these would perhaps reveal too much about the algorithm if they were made into preconditions.

All of the assumptions seem necessary for OpenJML to verify the method, as deleting any of them leads to potential overflow or underflow errors.

Since the method is changing the field `sum` that is declared outside of the method, a [frame condition](https://openjml.org/tutorial/FrameConditions) would normally be needed to completely specify the method.

**Learning Objectives:** 

+ Understand how to handle potential overflow and underflow errors.
+ Understand the difference between JML and Java arithmetic.

## **Question 2**
**(a) The function given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
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
**Answer and Explanation:**
First let's assess what the current preconditions are requiring of both `playerHealth` and `dmg`. The first precondition requires that `dmg` be a negative number. Next, the program requires that `playerHealth` be greater than or equal to zero. Now, within the function we check if `playerHealth` is greater than `dmg`, and if it is we return `playerHealth - dmg`, otherwise we return zero - since the player would be dead if their health is less than the `dmg` attack or zero.
 
Can you determine the error in the preconditions given the code? Notice how we require that `dmg` be negative but we return `playerHealth - dmg`, which would mean we are actually returning `playerHealth - (-dmg)` = `playerHealth + dmg` (since `dmg` has to be negative). This would cause an error since we would now potentially have an overflow error since we are adding `dmg` to `playerHealth` and `playerHealth` is not bounded with `Integer.MAX_VALUE`. To fix this we need to require that `dmg` be a positive number since it is we are subtracting `dmg` from `playerHealth`. So we write the following:
```Java
//@ spec_public
private int playerHealth;
	
//@ requires 0 <= dmg < Integer.MAX_VALUE;
//@ requires 0 < playerHealth;
public int updatePlayerHealth(int dmg) {
	if(playerHealth > dmg) {
		return (playerHealth - dmg);
	}else {
		return 0;
	}
}
```
**(b) How could you edit the code to verify the function with the original specification?**

**Asnwer and Explanation:**
To keep the original preconditions without errors we would have to make a small edit to the code. The original problem with the function was that `playerHealth - (-dmg)` = `playerHealth + dmg`. So if we want to require that `dmg` be negative we need to change the return to `playerHealth + dmg` so that `playerHealth + (-dmg)` = `playerHealth - dmg`. So we can write the following:
 ```Java
 //@ spec_public
private int playerHealth;
	
// @ requires dmg <= 0;
//@ requires 0 < playerHealth;
public int updatePlayerHealth(int dmg) {
	if(playerHealth > dmg) {
		return (playerHealth + dmg);
	}else {
		return 0;
	}
}
 ```
**Learning Objective:** 
The goal of this exercise is to see if the student understands how they need to account for OpenJML testing all possible inputs that conform to the preconditions. While the exercises focuses on using the correct opteration we want to show the student how not using the correct operation would cause error. Given the preconditions and the code in part (a) the student needs to recognize that since OpenJML will test negative values for `dmg` it will cause overflow warnings because with the code it returns `playerHealth + dmg`. Additionally, in part (b) we want to see if the student understands how the original precondition can still be used to have the same result if the code makes sense with the input OpenJML passes in. At this point in the students studies they have seen numerous examples of potential overflow errors and how to handle them, so this should be an easier exercise.
