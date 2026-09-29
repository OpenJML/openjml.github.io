---
title: JML Tutorial - Exercises - Visibility
---
# Visibility Exercises:
## [Visibility Tutorial](https://www.openjml.org/tutorial/Visibility)

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

## **Question 2**
**The following has a visibility error. Fix it by giving the `represents` clause and appropriate visibility.**

```
public class Counter {
    //@ public model int count;
    private int _count = 0; //@ in count;

    //@ represents count = _count;

    //@ requires count < Integer.MAX_VALUE;
    //@ assignable count;
    //@ ensures count == \old(count+1);
    public void inc() {
        _count++;
    }
}
```

**Learning Objectives:**
+ Understand how visibility works with JML specifications
+ Understand how to use the `spec_public` modifier
+ Understand the rule for visibility of `represents` clauses
+ Gain more experience with using the `assigns` clause

## Resources
+ [VisibilityExample1 file](VisibilityExample1.java)
+ [Counter file](Counter.java)

## **[Answer Key](VisibilityExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
