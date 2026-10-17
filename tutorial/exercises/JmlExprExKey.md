---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises Key:
## [JML Expressions Tutorial](https://www.openjml.org/tutorial/Expressions)

## **Question 1**
First we need to see if we understand what the method is doing. The loop runs from 2 to `num/2`, which is valid because a number is never divisible by more than half of itself.

Thus we can write the assertion about `num` shown below.
```Java
public boolean primeChecker(int num) {
        //@ assume 0 < num;
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i < num/2;
                //@ assume !(\exists int j; 2 <= j < i; num % j == 0);
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime && 2 <= i < num/2;
                //@ assert !(\exists int j; 2 <= j < i; num % j == 0);
	}
        //@ assume isPrime && 2 <= i && i == num/2;
        //@ assume !(\exists int j; 2 <= j < i; num % j == 0);
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert isPrime;
        //@ assert !(\exists int j; 2 <= j <= num/2; num % j == 0);
	return isPrime;
}
```

The last assertion uses the `\exists` expression. If there was did exist a small factor that evenly divides `num`, then the code should have returned false before the last assertion. 

**Learning Objective:** 
The objectives of this exercise are to:
+ Gain experience with quantified expressions
+ Gain experience with JML operators.

## **Question 2**
One way to write such a function is as follows.

```Java 
    public boolean modusPonens(boolean p, boolean q) {
        if (p) {
            //@ assert q <==> (p ==> q);
            return q;
        } else {
            //@ assert p ==> q;
            return true;
        }
    }
```
Note that the Boolean expression `q` is equivalent to `q == true` and that when `p` is false (e.g., in the else case), then `!p <==> (p ==> q)` is equivalent to `true <==> (p ==> q)`, which is also equivalent to `p ==> q`.


Before we move on, take a look at these other correct implementations of Modus Ponens:

**Version 1:** 
The following version uses the tautology that `p ==> q` is equivalent to `(!p || q)`. This can be seen from [the truth table](JmlExprEx). Note that `(!p | q)` would also be equivalent in this context.
```Java
    public boolean modusPonens(boolean p, boolean q) {
        //@ assert (!p || q) <==> (p ==> q);
        return !p || q;
    }
```

**Version 2:** 
The following is a more concise way of stating the first answer, using Java's `?` `:` expression.
```Java
    public boolean modusPonens(boolean p, boolean q) {
        //@ assert (p ? q : true) <==> (p ==> q);
        return p ? q : true;
    }
```

You may want to revisit this exercises after learning about [postconditions](https://openjml.org/tutorial/Postconditions.html), as the same postcondition, namely `\result <==> (p ==> q)` would work for all versions of the correct code.

**Learning Objective:** 
The goal of this exercise is to further check if the student understands how JML operators work. 

## Resources
+ [JML Expressions Exercises](JmlExprEx)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
