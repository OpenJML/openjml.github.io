---
title: JML Tutorial - Exercises - Arithmetic
---
# Arithmetic Exercises Key:
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
**Asnwer and Explanation:**
First let’s break down the code. The function `sumThreeNums()` takes in three integer variables `n1`, `n2`, and `n3` and will add them together and set the global variable `sum` equal to the result. We are given our postoncdition of the function which states that `sum` must be greater than zero and less than `Integer.MAX_VALUE`. `Integer.MAX_VALUE` is simply a variable of the class Integer that is the largest possible value of type int. If we were to run this code using OpenJML we would get many warnings concerning the Arithmetic Operation Range. What this means is essentially OpenJML cannot verify that the function will not have any overflow or underflow errors when it passes in all possible inputs. So we need to tell OpenJML what our range of `n1`, `n2`, and `n3` can be. 

 Given the postcondition that `sum` must be less than `Integer.MAX_VALUE` we can determine that all of our integers passed in must also be less than `Integer.MAX_VALUE` otherwise one variable on it’s own will cause an overflow error because it could be greater than the largest value of type int. Additionally, we are told that sum must be greater than zero, so we also need to reflect this in our requirements for out integer variables passed in. As such, we can write something like the following: 
```Java
public class ArithmeticExample1 {
	//@ spec_public
	private int sum;

	//@ requires 0 < n1 < Integer.MAX_VALUE;
	//@ requires 0 < n2 < Integer.MAX_VALUE;
	//@ requires 0 < n3 < Integer.MAX_VALUE;
	//@ ensures 0 < sum < Integer.MAX_VALUE;
	public void sumThreeNums(int n1, int n2, int n3){
		sum = n1 + n2 + n3;
	}	
}
```
While we might think we are done, we are not. OpenJML still cannot verify tht **adding** all of these numbers together won’t cause and overflow or underflow error so let’s take care of that. Let’s take a look at what `sum` is equal to in our function. In our function `sum = n1 + n2 + n3`, therefore, we need to make sure that `n1 + n2 + n3` is less than `Integer.MAX_VALUE`. We might say `(n1 + n2 + n3) < Integer.MAX_VALUE` but this on its own isn’t really doing anything we haven’t said. Let’s rework it to be `n1 < Integer.MAX_VALUE/(n2 + n3)` which we know is valid because of Alegrba. However, now OpenJML cannot verify that `n2 + n3` isn’t greater than or equal to `Integer.MAX_VALUE` so we need to check that `n2 < Integer.MAX_VALUE/n3`. Note, we don’t have to worry about dividing by zero since we explicitly stated that our numbers are greater than zero -  if we didn’t do this it would cause warnings of possible divisions by zero. 

Also, note that we are modifying the memory of global variable `sum` and should therefore specify this in our speicifations. That being said, let’s write the following:
```Java
public class ArithmeticExample1 {
	//@ spec_public
	private int sum;

	//@ requires 0 < n1 < Integer.MAX_VALUE;
	//@ requires 0 < n2 < Integer.MAX_VALUE;
	//@ requires 0 < n3 < Integer.MAX_VALUE;
	//@ requires n2 < Integer.MAX_VALUE/n3;
	//@ requires n1 < Integer.MAX_VALUE/(n2 + n3);
	//@ assigns sum;
	//@ ensures 0 < sum < Integer.MAX_VALUE;
	public void sumThreeNums(int n1, int n2, int n3){
		sum = n1 + n2 + n3;
	}	
}
```
**Learning Objective:** 
The goal of this exercise is to make the student more comfortable with handling potential overflow and underflow errors. We want the student to be aware the while the compiler will not throw any errors about overflow/underflow errors, OpenJML will test all possible inputs and therefore if the student doesn’t specify the range of their variables it won’t verify. We also introduce the student to `Integer.MAX_VALUE` and ask them to think critically about the steps needed to verify the function. The student should recongize that in order for `n1 + n2 + n3` to be less than `Integer.MAX_VALUE` we need to make sure that `n2 + n3` is less than `Integer.MAX_VALUE`. This exercise also gives the student more experience with the `assigns` clause. 

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
**Asnwer and Explanation:**
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

## **Resources:**
+ [Arithmetic Exercises](ArithmeticEx.md)
+ [Question 1 Java](ArithmeticExample1.java)
+ [Question 2 Java](ArithemticExample2.java)
