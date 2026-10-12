---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises Key:
## [Assert Statements Tutorial](https://www.openjml.org/tutorial/AssertStatement)

## **Question 1**
One way to write assertions that verify is as follows.
```Java
public class AssertExample1 {

    private int max;

    public void max3(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert here
            //@ assert max >= a && max >= c && max == a;
        } else if (b >= a && b >= c) {
            max = b;
            // second assert here
            //@ assert max >= a && max >= b && max == b;
        } else {
            max = c;
        }
        // third assert here
        //@ assert max >= a && max >= b && max >= c && (max == a || max == b || max == c);
    }

}
```

First, let’s understand what the code is doing. The method `max3` takes in three integer numbers `a`, `b`, and `c`, then compares each integer against the other two. When comparing the integers the `>=` operator is used, since we were not told that each integer would be distinct from the others. We are not given any definite pre- or postconditions that need to be met, but we are told to write the strongest assert statements that verify where indicated. Remember that `assert` is used when a condition is expected to hold in body of a method.

The third assert statement (at the end of the method body) says that the value of `max` is greater than or equal to all of the arguments and is equal to one of them. Do you see why the disjunction `max == a || max == b || max == c` is valid? What kinds of coding errors could that disjunction prevent?

## **Question 2**
One way to write these assertions is the following.

```Java
public class AssertExample2 {
    
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

}
```

The method `primeChecker` checks if a number passed in is prime, and returns `true` just when it is. The `assume` statements are needed to check this code without being warned about: possible division by zero and that the loop body possibly not maintaining the value of `isPrime` when it loops another time (see [the section on specifying loops](https://openjml.org/tutorial/Loops.html) for more about loop invariants).  This is the reason for some of the assume statements; do you see why they are valid? (On the other hand, it might indeed be better to avoid using the variable `isPrime` completely; do you see how to do that?)

For the assertions, we know that the method will stop and return `false` if it finds that `num` is evenly divisible by an integer between 2 and the `num/2`. Thus, if the function runs through the entire for-loop and the following if-statement, it returns `true`, since then `num` must be prime. So, we can assert that the function will set `isPrime` to `false` if `num % i == 0` (for some integer `i` between 2 and `num/2`, inclusive).

It is possible to summarize the effects of this code in several different ways. See [the section on postconditions](https://openjml.org/tutorial/Postconditions.html) for a way to summarize the code in a postcondition. You might also want to return to this example after learning how to [specify loops](https://openjml.org/tutorial/Loops.html). Note that `isPrime == true` is equivalent to the boolean variable `isPrime` and similarly when `isPrime == false` is equivalent to `isPrime` (when `isPrime` is false).

## **Resources:**
+ [Assert Statements Exercises](AssertEx.md)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
