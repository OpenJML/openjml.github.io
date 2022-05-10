---
title: JML Tutorial - Exercises - Visibility
---
# Visibility Exercises:
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

**Learning Objectives:**
+ Understand how visibility works with JML specifications
+ Understand how to use the `spec_public` modifier 
+ Gain more experience with using the `assigns` clause

## **[Answer Key](VisibilityExKey.md)**

