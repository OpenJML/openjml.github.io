---
title: JML Tutorial - Exercises - Visibility
---

## [Tutorial](https://www.openjml.org/tutorial/Visibility)

## **Question 1**

Since the [code in the example](VisibilityExample1.java) is unable to be verified with its current specifications, let's first understand what the code is doing and then find where the specifications are failing. The program has two private `int` variables `MAXHEALTH` and `playerHealth`. The function `damage()` takes in an integer value and will deduct it from the player’s health so long as `playerHealth` is greater than the `dmg` to be done; otherwise we set the `playerHealth` to zero. The next function `heal()` takes in an integer value `hp` which will be added to the player's health if `playerHealth + hp` is less than the `MAXHEALTH`. However, if we try to run the program with the current specifications we get the error that the identifiers `playerHealth` and `MAXHEALTH` are of private visibility and cannot be used in specifications with public visibility (which is the default for specifications cases of public methods that do not explicitly use a visibility modifier). So we have to change the visibility of `playerHealth` and `MAXHEALTH` to public for the specifications. However,  we don't do this by changing the actual code, as this would change the program's design. Instead we use the `spec_public` modifier. Additionally, note how we are modifying `playerHealth` in both functions, so we should also specify that we are assigning `playerHealth`. With that being said we can write the following:
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

## **Question 2**

The visibility of a `represents` clause should be that of the least visible field mentioned, hence in this instance, the visibility should be `private` as in the following.

```
public class Counter {
    //@ public model int count;
    private int _count = 0; //@ in count;

    //@ private represents count = _count;

    //@ requires count < Integer.MAX_VALUE;
    //@ assignable count;
    //@ ensures count == \old(count+1);
    public void inc() {
        _count++;
    }
}
```
