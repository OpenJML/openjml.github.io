---
title: JML Tutorial - Exercises - Visibility
---
# Visibility Exercises Key:
## **Question 1**
**The program given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
```Java
public class VisibilityExample1 {

	private static int MAXHEALTH = 100;
	private int playerHealth = 100;
	
	//@ requires 0 <= dmg < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	public void damage(int dmg) {
		if (playerHealth > dmg) {
			playerHealth -= dmg;
		} else {
			playerHealth = 0;
		}
	}

	//@ requires 0 <= hp < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	//@ requires playerHealth + hp < MAXHEALTH;
	//@ ensures playerHealth <= MAXHEALTH;
	public void heal(int hp) {
		if (MAXHEALTH >= (playerHealth + hp)) {
			playerHealth += hp;
		}
	}

}
```
**Asnwer and Explanation:**
The code above is unable to be verified with its current specifications, let's first understand what the code is doing and then find where the specifications are failing. The program has two private int variables `MAXHEALTH` and `playerHealth`. The function `damage()` takes in an integer value and will deduct it from the player’s health so long as `playerHealth` is greater than the `dmg` to be done - in which case we set the `playerHealth` to zero. The next function `heal()` takes in an integer value `hp` which will be added to the player's health if `playerHealth + hp` is less than the `MAXHEALTH`. However, if we try to run the program with the current specifications we get the error that the identifiers `playerHealth` and `MAXHEALTH` are of private visibility and cannot be used. So we have to change the visibility of `playerHealth` and `MAXHEALTH` to public for the specifications. However,  we don't do this by changing the actual code, as this would cause errors down the line. Instead we use the `spec_public` modifier. Additionally, note how we are modifying `playerHealth` in both functions, so we should also specify that we are assigning `playerHealth`. With that being said we can write the following:
```Java
public class VisibilityExample1 {

	//@ spec_public
	private static int MAXHEALTH = 100;
	//@ spec_public
	private int playerHealth = 100;
	
	//@ requires 0 <= dmg < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	//@ assigns playerHealth;
	public void damage(int dmg) {
		if (playerHealth > dmg) {
			playerHealth -= dmg;
		} else {
			playerHealth = 0;
		}
	}

	//@ requires 0 <= hp < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	//@ requires playerHealth + hp < MAXHEALTH;
	//@ assigns playerHealth;
	//@ ensures playerHealth <= MAXHEALTH;
	public void heal(int hp) {
		if (MAXHEALTH >= (playerHealth + hp)) {
			playerHealth += hp;
		}
	}

}
```
**Learning Objective:** 
The goal of this exercise is to test if the student understands when to specify the visibility of something when trying to write specifications. In this case the code cannot verify because in our pre and postconditions we are using `playerHealth` and `MAXHEALTH`, but both of these are of private visibility in the program. While this won't cause an issue with the actual code, these variables are still considered private to the specifications even though they are in the same class with them. Additionally, the student should recognize that we are modifying the value of `playerHealth`, and it is therefore important to note this in our specifications as well.

## **Resources:**
+ [Visibility Exercises](VisibilityEx.md)
+ [Question 1 Java](VisibilityExample1.java)

