--
title: JML Tutorial - Answers to Postcondition Exercises
--
## [Postconditions Exercises](https://www.openjml.org/tutorial/exercises/PostCondEx)

## **Question 1**
**(a) This would fail to verify because when the value of `num` was greater than `Integer.MAX_VALUE/2`, then the code `num*2` would cause an integer overflow, resulting in a negative number, which was less than the argument `num`.

To check this, observe that the output of running `openjml --esc` on the JML+Java in the exercise is as follows.

```
{% include_relative PostCondEx1a.out %}
```
