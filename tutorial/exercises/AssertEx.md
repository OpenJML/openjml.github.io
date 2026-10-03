---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises:
## [Assert Statements Tutorial](https://www.openjml.org/tutorial/AssertStatement)

## **Question 1**
**Given the code below, write specifications to verify the function max, including the assert statements where indicated. See [the tutorial on visibility](https://openjml.org/tutorial/Visibility.html) for the meaning of the `spec_public` annotation, which is not important for this exercise.**
```Java
public class AssertExample1 {

    private /*@ spec_public @*/ int max;

    public void max(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert
        } else if (b >= a && b >= c) {
            max = b;
            // second assert
        } else {
            max = c;
        }
        // third assert
    }

}
```

**Learning Objectives:** 
+ Understand how `assert` can be used
+ Understand the relationship between `assert` statements and postconditions 

## **Question 2**
**Given the function below, write the strongest[^1] assert statements that will pass at the places indicated.**

[^1]: An assert statement `assert P;` is stronger than assert statement `assert Q;` when the predicate `P` is stronger than the predicate `Q` (that is, when `P` implies `Q`). See [the tutorial section on preconditions](https://www.openjml.org/tutorial/Preconditions.html) for more about the strength of predicates.

```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean isPrime;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//first assertion here
			isPrime = false;
			//second assertion here 
			return isPrime;
		}
	}
	
	isPrime = true;
	//third assertion here
	return isPrime;
}
```
**Learning Objectives:** 
+ Gain more experience writing `assert` statements

## **[Answer Key](AssertExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Java code for question 1](AssertExample1.java)
+ [Java code for question 2](JMLExprExample1.java)

## Footnotes
