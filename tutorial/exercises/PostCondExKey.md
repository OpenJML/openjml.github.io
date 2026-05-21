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
