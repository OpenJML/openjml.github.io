---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises Key:
## [Assert Statements Tutorial](https://www.openjml.org/tutorial/AssertStatement)

## **Question 1**
One way to write assertions that verify is as follows.
```Java
public class AssertExample1 {

    private /*@ spec_public @*/ int max;

    //@ ensures max >= a && max >= b && max >= c;
    public void max3(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert
            //@ assert max >= a && max >= c;
        } else if (b >= a && b >= c) {
            max = b;
            // second assert
            //@ assert max >= a && max >= b;
        } else {
            max = c;
        }
        // third assert
        //@ assert max >= a && max >= b && max >= c;
    }

}
```

**Answer and Explanation:**
First, let’s understand what the code is doing. The method `max3` takes in three integer numbers `a`, `b`, and `c`, then compares each integer against the other two. When comparing the integers the `>=` operator is used, since we were not told that each integer would be distinct from the others. We are not given any definite pre or postconditions that need to be met, but we are told to write the appropriate assert statements where indicated. Remember that `assert` is used when a condition is expected to "hold at a point within the body of a method."

An equivalent to the third `assert` (at the end of the method body) would be a postcondition, which could be as shown in the ensures clause of `max3` above. Also, both the assert and the postcondition can be included, but once there is a postcondition, the third assert becomes redundant.

Note that in JML, one cannot use `\result` (see [the tutorial section on postconditions](https://openjml.org/tutorial/Postconditions.html)) in a postcondition for a method that is `void`, like `max3` in this exercise. If you know about `\result` already, think of the field `max` as holding the result of the method's computation.

Furthermore, since the field `max` is declared outside the method as `private` but the field is used in a public specification there would be a visibility problem in JML (see [the tutorial section on visibility](https://openjml.org/tutorial/Visibility.html) for details). This is the reason that the field `max` is declared to be `spec_public`.

## **Question 2**
**Given the function below, write the strongest assert statements that will pass at the places indicated.**
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
**Answer and Explanation:**
The function above checks if a number passed in is prime or not, and returns `flag =  true` if it is, and `flag = false` if it's not. We are already given some specifications needed to run this program without any warnings. However, we are asked to determine and include any assertions that can be made. We know that the function will stop and return `flag = false` if it finds that `num` is divisible by anything other than one and itself. If the function runs through the entire for-loop without finding that `num` is divisible by anything other than one and itself, it returns `flag = true` - in other words it has concluded that `num` is a prime number. So, we can assert that the function will set `flag` to false if `num % i == 0`, and we can also assert that `flag` will be set to true if the function runs through the for-loop without stopping. So we can write the following:
```Java
//@ requires num > 0;
//@ ensures \result <==> !(\exists int i; i >= 2; num % i == 0);
public boolean primeChecker(int num) {
	boolean isPrime;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			//@ assert isPrime == false;
			return isPrime;
		}
	}
	
	isPrime = true;
	//@ assert isPrime == true;
	return isPrime;
}
```

**Learning Objective:** 
The goal of this exercise is to see if the student can identify what assertions can be made at certain points in the code. To avoid confusion the student is told where in the code the assert is meant to me added. This exercise also checks that the student understand that we cannot assert false because this will cause an error in OpenJML, which is why we assert that the variable flag can be false.

## **Resources:**
+ [Assert Statements Exercises](AssertEx.md)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
