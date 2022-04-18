---
title: JML Tutorial - JML's \bigint built-in integer type
---

`\bigint` is the type of unbounded, mathematical integers. Most typically when writing specifications, users think in terms in mathematical integers and
the limitations of fixed bit-widths are an afterthought. Mathematical integers are also easier for solvers to reason about, so using them is natural 
in writing specifications. They are similar to Java's `BigInteger`, except that no actual computation is being done, only logical reasoning.

Since `\bigint` is a JML built-in type, it may only be used within specifications. But that includes using it as the type of ghost fields, ghost variables 
and the
parameters and result types of model methods.

The `\bigint` built-in type is intuitive and natural to use, but for the sake of clarity, its operations are listed here. `j` and `k` are two values of
type `\bigint` and `i` a value of a Java numeric type.
* `j == k` and `j != k` mean equality and inequality
* `- j` is mathematical integer negation`
* `j + k` is mathematical integer addition
* `j - k` is mathematical integer subtraction
* `j * k` is mathematical integer multiplication
* `j / k` is mathematical integer division (truncation toward zero); `k` must not be 0; `j/k` is negative or zero if `j` and `k` have different signs and is positive or zero if `j` and `k` have the same sign
* `j % k` is mathematical integer modulo, but is similar to Java's `%` operation: `k` may not be zero, `j%k` has the same sign as `j` and is independent of the sign of `k`, and for `k != 0`, `(j/k)*k + (j%k) == j`
* `<` and `<=` and `>` and `>=` have their expected meanings with the result type being boolean
* casts are allowed to and from other numeric types, such as `(\bigint)i` or `(int)j`. When casting from `\bigint` to a bounded type, a range check is performed, depending on the [arithmetic mode](ArithmeticModes).

TODO - example?

TODO - library of built-in functions