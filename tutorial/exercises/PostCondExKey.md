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

**(b)** 
A simple fix to the postcondition is to change `<` to `<=`, which will allow the method to return 0 when the argument is 0. This directly addresses the problem noted above.

## **Question 2**
A postcondition that can be used to make the code verify is `\result == num / 2`.
(Any equivalent expression will do, including `2*\result == num`, 
but the theorem provers, SMT solvers, used in OpenJML cannot reason about
multiplication and division,
so OpenJML will complain about that form of the postcondition.)

## **Question 3**

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

## **Question 4**

The answer can vary, but one possible specification and implementation is the following.
```
    /*@ requires !Double.isNaN(x);
      @ requires !Double.isNaN(y);
      @ ensures Math.abs(\result - (x+y)/2.0) < 0.001; @*/
    public double average(double x, double y) {
        return (x+y)/2.0;
    }
```

(Currently, in OpenJML 21.0.26.a, the requires clauses are not needed, but it is always good practice to rule out NaN, so that the postcondition has a chance of being true.)

Notice that the specification above only requires that the result be approximately equal to the expected value. Since floating point arithmetic is only an approximatino of real arithmetic, it is best to never compare floating point numbers for equality.
