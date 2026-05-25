--
title: JML Tutorial - Exercises - Answers to Precondition Exercises
--
## [Precondition Exercises](https://www.openjml.org/tutorial/exercises/PreCondEx)

## **Question 1**
We know that the method takes three parameters, the current amount in the user's bank account, the price of an item, and the number of items to be purchased. To ensure the bank account is never negative, we need to check the following:
1. the current amount in the user's bank account is greater to zero;
2. the cost of one item is greater than or equal to zero; and
3. that purchasing n items doesn't make the user's bank account negative.
If all these requirements are met, we can ensure that the user's bank account will not be below $0.00. 

However, it is important to note that since we are dealing with floating points (doubles in this case) we need to ensure that the inputs passed into the function are not NaN. This can be done using the function `isNan()` of the class Double which can be used to check if the inputs `bankAccount` or `price` in this case are `NaN`.
By doing this we can avoid potential problems if a user were to pass in a `NaN` value. OpenJML will not check for `NaN` inputs on its own, so it is important to include this requirement when working with floating point numbers
to avoid potential errors.
In the following we use two requires clauses for these checks, but one could equivalently use one clause, such as the following.
```
requires !Double.isNaN(bankAccount) && !Double.isNaN(price);
```
or one could use a logically equivalent form such as
```
requires !(Double.isNaN(bankAccount) || Double.isNaN(price));
```

(There is one advantage to using two separate requires clauses, however, which is that error messages for calls to the method that attempt to pass NaN to either arugment will be easier to understand when separate requires clauses are used.
Thus our preferred solution is equivalent to the following.)

```Java
//@ requires !Double.isNaN(bankAccount);
//@ requires bankAccount > 0.0;
//@ requires !Double.isNaN(price);
//@ requires price >= 0.0;
//@ requires (price*n) <= bankAccount;
//@ ensures \result >= 0.0;
public double bankUpdate(double bankAccount, double price, int n) {
	bankAccount = bankAccount - (price*n);
	return bankAccount;
}
```

**Incorrect Version 2:**

If the specification doesn't require `bankAccount >= 0.0`, then there is no way the user can purchase the items because they would not have the funds for the purchase. Additionally, we use `>= 0.0` because it is valid for a bank account to hold $0.00.

**Incorrect Version 3:**

The specification must require that `price >= 0.0`, because negative prices would actually add money to the resulting account balance.

Why is it okay to specify that the price may be $0.00?

## **Question 2**

A simple answer is equivalent to the following.
```
//@ requires 0 < a.length;
```

Requiring that the array has at least one argument guarantees that the expression `a[0]` is well-defined.
Note that in JML it is already implicit that the array argument `a` is not null, so there is no need to specify that.

(Any logically equivalent form of the precondition expression would work,
such as `a.length > 0`. However, we think it good style to follow Rustan Leino's idea of writing such expressions with the smallest quantity on the left, so the expression `1 <= a.length` would be equally good.)

## **Question 3**

As Bertrand Meyer points out in his book _Object-oriented Software Construction_[^1], the precondition of the strongest possible specification would be one that allows it to always be called, i.e., _true_, since that is implied by every predicate and so is the weakest possible predicate. A suitable postcondition would be the strongest possible, and thus impossible to achieve, i.e., _false_, since that predicate implies all others.

[^1]: Bertrand Meyer, _Object-Oriented Software Construction_ (Second Edition), section 11.3, especially pp. 335-336.

## **Question 4**

The precondition of the weakest possible specification would be one that would never allow the method to be called, i.e., _false_. A suitable postcondition would be _true_, since that imposes no burden on the developer.
