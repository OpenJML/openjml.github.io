--
title: JML Tutorial - Exercises - Answers to Precondition Exercises
--
## [Precondition Exercises](https://www.openjml.org/tutorial/exercises/PreCondEx)

## **Question 1**

A simple answer is equivalent to the following.
```
//@ requires 0 < a.length;
```

(Any logically equivalent form of the precondition expression would work,
such as `a.length > 0`. However, we think it good style to follow Rustan Leino's idea of writing such expressions with the smallest quantity on the left, so the equivalent expression `1 <= a.length` would be preferred.)

This requires clause can be seen in the following code.
```Java
    //@ requires 0 < a.length;
    public int element0(int a[]) {
        return a[0];
    }
```

Requiring that the array has at least one element guarantees that the expression `a[0]` is well-defined.
Note that [in JML it is already implicit that the array argument `a` is not null](https://openjml.org/tutorial/Nullness), so there is no need to specify that.

## **Question 2**
We know that the method takes three parameters, the user's current balance, the price of an item, and the number of items to be purchased. To ensure the balance is never negative, we require the following:

a. the user's current balance is non-negative;

b. the price is at least 0;

c. the number of items is positive;

c. that purchasing n items doesn't make the user's balance negative or increase.

If all these requirements are met, the assertion in the code will pass.

However, it is important to note that, since we are dealing with floating point numbers, the specification must require that the arguments passed in are not NaN (otherwise the assertion may fail). This can be done using the method `isNaN()` of the class `Double` which is used require that both the inputs `balance` and `price` are not NaN.
By requiring that the double arguments not be NaN, the specification operates in a more logical manner, and the user will get a verification error if they pass in a value that could be NaN. (OpenJML does not prohibit NaN arguments by default.) 
In the following we use two requires clauses for these checks, but one could equivalently use one clause, such as the following.
```
requires !Double.isNaN(balance) && !Double.isNaN(price);
```
Or equivalently the following.
```
requires !(Double.isNaN(balance) || Double.isNaN(price));
```

However, in our preferred solution below, we use separate requires clauses stating that each double argument must not be NaN. One advantage to using two separate requires clauses, is that verification error messages for calls to the method that could pass NaN to either argument will be easier to understand.

```Java
    //@ requires !Double.isNaN(balance);
    //@ requires 0.0 <= balance;
    //@ requires !Double.isNaN(price);
    //@ requires 0.0 <= price;
    //@ requires 0 < n;
    //@ requires (price*n) <= balance;
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;
	return balance;
    }
```

Note that we use `0.0 <= balance` because a balance might be zero, and that would suffice to purchase an item that is free.  The preconditions requiring the price to be non-negative and the quantity to be positive, together with the precondition `(price*n) <= balance` do, however, require that the balance is sufficient to purchase the given number of items.

**Incorrect Version 2:**

An incorrect solution is as follows.

```
    //@ requires !Double.isNaN(balance);
    //@ requires 0.0 <= balance;
    //@ requires !Double.isNaN(price);
    //@ requires 0.0 <= price;
    //@ requires 0 < n;
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
```

The above specification doesn't require `(price*n) <= balance`, so the balance might not be enough to purchase the given number of items at the given price. Trying to verify this results in the following output.

```
{% include_relative PreCondEx2Wrong.out %}
```

**Incorrect Version 3:**

Another incorrect answer is as follows.

```Java
    //@ requires !Double.isNaN(balance);
    //@ requires 0.0 <= balance;
    //@ requires !Double.isNaN(price);
    //@ requires (price*n) <= balance;
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
```

Since this specification does not require `0.0 <= price` and `0 < n`, the result of (price*n) could be negative, which would actually add money to the balance.

The following are some additional questions to think about.

Why is it okay to specify that the price may be $0.00?

What would happen if the assertion in the body of the method were written as

```
        //@ assert 0.0 <= balance;
```
instead of also asserting that `balance <= oldBalance`?

## **Question 3**

As Bertrand Meyer points out in his book _Object-oriented Software Construction_[^1], the precondition of the strongest possible specification would be one that allows it to always be called, i.e., `true`, since that is implied by every predicate and so is the weakest possible predicate. A suitable postcondition would be the strongest possible, and thus impossible to achieve, i.e., `false`, since that predicate implies all others.

[^1]: Bertrand Meyer, _Object-Oriented Software Construction_ (Second Edition), section 11.3, especially pp. 335-336.

## **Question 4**

The precondition of the weakest possible specification would be one that would never allow the method to be called, i.e., `false`. A suitable postcondition would be `true`, since that imposes no burden on the developer.
