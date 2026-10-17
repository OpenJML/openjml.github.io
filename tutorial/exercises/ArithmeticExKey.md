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

Since the method is changing the field `sum` that is declared outside of the method, a [frame condition](https://openjml.org/tutorial/FrameConditions) would normally be needed to completely specify the method.

**Learning Objectives:** 

+ Understand how to handle potential overflow and underflow errors.
+ Understand the difference between JML and Java arithmetic.

## **Question 2**

(a) One way to add assume statements to allow the function to be verified is the following.
```Java
public class ArithmeticExample2 {
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
        //@ assume 0 <= dmg;
	//@ assume 0 < playerHealth;   
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}
```

The problem in the Java code is the possibility of making `playerHealth` such a large negative number that Java cannot represent it as an `int`. The assumptions added prevent that problem.
The first assume statement says that the argument `dmg` is non-negative, and the second says that `playerHealth` is positive. Thus, in Java's 2's-complement arithmetic, `playerHealth` is at least 1 and `dmg` is at most `Integer.MAX_VALUE`; so the subtraction implicit in the assignment, `playerHealth - dmg`, can only reduce the value of `playerHealth` to `1 - Integer.MAX_VALUE`, which is representable as an `int`. The first assumption would be appropriate as a [precondition](https://openjml.org/tutorial/Preconditions.html). The assumption that `0 < playerHealth` might also be appropriate as a precondition, but perhaps a more standard way of specifying such a property would be to use an [invariant](https://openjml.org/tutorial/Invariants.html).

Note that there is no need to constrain `dmg` to be at most `Integer.MAX_VALUE` as it is an `int` argument, so it must fit into an `int`.

(b) One solution for rewriting the code, without specifications is as follows.

 ```Java
public class ArithmeticExample2 {
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
        if (dmg < 0 || playerHealth <= 0) {
            return playerHealth;
        }
        // here 0 <= dmg && 0 < playerHealth;
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}
```

As the comment above the original code indicates, the if-statement that tests the values of `dmg` and `playerHealth` ensures the same conditions that the assume statements of the solution to part (a), above. Indeed, this comment could be turned into a JML assert statement, which would verify at that point. The if-statement thus prevents the value of the computation `playerHealth - dmg` from having any underflow problem.

The above code rewrite might make sense if the method could be called by untrusted clients.  If the method were only called by trusted code (e.g., if the method itself had protected visibility), then using preconditions might be a better solution, as there would be no runtime computation involved.

