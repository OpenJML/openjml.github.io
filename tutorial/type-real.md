---
title: JML Tutorial - JML's \real built-in mathematical real type
---

`\real` is the type of mathematical real numbers. Mathematical reals are easier for solvers to reason about than floating point numbers, so using them is natural 
in writing specifications.

Since `\real` is a JML built-in type, it may only be used within specifications. But that includes using it as the type of ghost fields, ghost variables 
and the
parameters and result types of model methods.

The `\real` built-in type is intuitive and natural to use, but for the sake of clarity, its operations are listed here. `j` and `k` are two values of
type `\real`.
* `j == k` and `j != k` mean equality and inequality
* `- j` is mathematical real negation
* `j + k` is mathematical real addition
* `j - k` is mathematical real subtraction
* `j * k` is mathematical real multiplication
* `j / k` is mathematical real division (not rounded to an integer); `k` must not be 0
* `j % k` is mathematical real modulo, but is similar to Java's `%` operation: `k` may not be zero, `j%k` has the same sign as `j` and is independent of the sign of `k`, and for `k != 0`, `(j/k)*k + (j%k) == j`.
* `<` and `<=` and `>` and `>=` have their expected meanings with the result type being boolean
* casts are allowed to and from other numeric types, such as `(\bigint)j`, which truncates towards zero.

```diff
! Caveat: Though real numbers are supported in OpenJML, the connection between real numbers and floating point numbers is incomplete and in some cases (such as handling NaN and infinite fp numbers) wrong
```

`\real` can be used like this:
```
//@ ghost \real r;
//@ ghost \real rr;
//@ set rr = r * 2;
```

As for `\bigint`, many of the methods in `java.lang.Math` have been specified for `real` values:
```
{% include_relative Real.java %}
```
