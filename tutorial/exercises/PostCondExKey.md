--
title: JML Tutorial - Exercises - Answers to Postcondition Exercises
--
## [Postconditions Exercises](https://www.openjml.org/tutorial/exercises/PostCondEx)

## **Question 1**
**(a)** This would fail to verify because when the value of `num` is zero, then the value returned (`num*2`) would not be strictly greater than `num`, as it would also be zero.

To check this, observe that the output of running `openjml --esc` on the JML+Java in the exercise is as follows. The second error message, which says that OpenJML cannot verify the postcondition is failing for precisely this reason. You can check this by adding a `show` statement before the return statement in the body, which will show that the counterexample is happening when `num` is 0.

```
{% include_relative PostCondEx1a.out %}
```

**(b)** A simple fix to the postcondition is to change `<` to `<=`, which will allow the method to return 0 when the argument is 0. This directly addresses the problem noted above.

## **Question 2**

As Bertrand Meyer points out in his book _Object-oriented Software Construction_[^1], the precondition of the strongest possible specification would be one that allows it to always be called, i.e., _true_, since that is implied by every predicate and so is the weakest possible predicate. A suitable postcondition would be the strongest possible, and thus impossible to achieve, i.e., _false_, since that predicate implies all others.

[^1]: Bertrand Meyer, _Object-Oriented Software Construction_ (Second Edition), section 11.3, especially pp. 335-336.

## **Question 3**

Again due to Bertrand Meyer's book, the precondition of the weakest possible specification would be one that would never allow the method to be called, i.e., _false_. A suitable postcondition would be _true_, since that imposes no burden on the developer. Meyer calls this "good work, if you can get it."

## **Question 4**

The answer to this question depends on the code you write. However, if you write the obvious body
```Java
    return w*h;
```
Then it is necessary to prevent integer overflow, so a precondition would be
```
   w*h <= Integer.MAX_VALUE
```
which could be put in a `requires` clause. A suitable postcondition for this would be
```
   \result == w*h
```
which could be put in an `ensures` clause.

Thus an entire solution could look like the following.

```Java
{% include_relative Rectangle.java %}
```

