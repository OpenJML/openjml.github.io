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

First, let’s understand what the code is doing. The method `max3` takes in three integer numbers `a`, `b`, and `c`, then compares each integer against the other two. When comparing the integers the `>=` operator is used, since we were not told that each integer would be distinct from the others. We are not given any definite pre or postconditions that need to be met, but we are told to write the appropriate assert statements where indicated. Remember that `assert` is used when a condition is expected to "hold at a point within the body of a method."

An equivalent to the third `assert` (at the end of the method body) would be a [postcondition](https://openjml.org/tutorial/Postconditions.html), which could be as shown in the ensures clause of `max3` above. Although both the assert and the postcondition can be included, once there is a postcondition, the third assert becomes redundant.

Note that in JML, one cannot use `\result` (see [the tutorial section on postconditions](https://openjml.org/tutorial/Postconditions.html)) in a postcondition for a method that is `void`, like `max3` in this exercise. If you know about `\result` already, think of the field `max` as holding the result of the method's computation.

Furthermore, since the field `max` is declared outside the method as `private` but the field is used in a public specification there would be a visibility problem in JML (see [the tutorial section on visibility](https://openjml.org/tutorial/Visibility.html) for details). This is the reason that the field `max` is declared to be `spec_public`.

## **Question 2**
One way to write these assertions is the following.

```Java
public boolean primeChecker(int num) {
        //@ assume num > 0;
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i;
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime;
	}
        //@ assume isPrime && 2 <= i;
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert isPrime;
	return isPrime;
}
```

The method `primeChecker` checks if a number passed in is prime, and returns `true` just when it is. The `assume` statements are needed to check this code without being warned about: possible division by zero and the fact that the loop body maintains the value of `isPrime` when it loops another time (see [the section on specifying loops](https://openjml.org/tutorial/Loops.html) for more about this).  (It might indeed be better to avoid using the variable `isPrime` completely; do you see how to do that?)

For the assertions, we know that the method will stop and return `false` if it finds that `num` is evenly divisible by an integer between 2 and the `num/2`. Thus, if the function runs through the entire for-loop and the following if-statement, it returns `true`, since then `num` must be prime. So, we can assert that the function will set `isPrime` to `false` if `num % i == 0` (for some integer `i` between 2 and `num/2`, inclusive), and we can also assert that `isPrime` will still be `true` if the function runs through the for-loop and the following if-statement without returning.

It is possible to summarize the effects of this code in several different ways. See [the section on postconditions](https://openjml.org/tutorial/Postconditions.html) for a way to summarize the code in a postcondition. You might also want to return to this example after learning how to [specify loops](https://openjml.org/tutorial/Loops.html). Note that `isPrime == true` is equivalent to the boolean variable `isPrime` (when `isPrime` is `true`) and similarly when `isPrime == false` is equivalent to `isPrime` (when `isPrime` is `false`).

## **Resources:**
+ [Assert Statements Exercises](AssertEx.md)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
