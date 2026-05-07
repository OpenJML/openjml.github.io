---
title: JML Tutorial - Well-Defined Expressions
---

Much confusion over error messages can be avoided by understanding that all JML expressions must be *well-defined*. Informally, one can think of a well-defined expression as one that, if it were a Java expression, would not throw an exception and would have an unambiguous meaning. JML requires that each expression in a JML context must be well-defined; the OpenJML tool will complain if it cannot prove that an expression is well-defined.

For example, `a[i]` is not well-defined if `i` is not in the range of the indices of `a`. So this example

```
{% include_relative T_WellDefined1.java %}
```

produces this result

```
{% include_relative T_WellDefined1.out %}
```

The output here deserves some explanation:
* First, OpenJML will continue looking for errors until it can find no more, but the order in which the errors are found is not guaranteed. So, the output you obtain by running the example above may have the error messages in a different order.
* The tool explores all possible paths in the method, using all possible values of the inputs that conform to the preconditions (an implicit precondition here is that `a` is non-null --- which we'll discuss later [null and non-null defaults](Nullness)).
* Now `a[i]` is well-defined only if `i` is in range for the array `a` (that is, `i` must necessarily be a legal index into `a`). But one possible combination of inputs is that `i` is actually in range, in which case the expression is well-defined and OpenJML goes on to see if the assertion can be proved true. As the precondition says nothing about the values in the array, the assertion cannot be proved true and a verification error message results.
* The other two cases are when `i` is too large (at least as large as `a.length`) or too small (`i` is negative). In these cases the expression is not well-defined; OpenJML issues verification errors calling out this undefinedness.

The rules for well-definedness of a JML expression build up from the leaves of the expression tree, with any compound expression requiring that each of its sub-expressions be well-defined. Note that even before OpenJML begins its work, an expression must not have any parse or type-checking errors. The following describes when particular kinds of expressions are well-defined:

* Literals (`true`, `false`, `null`, numbers and literal strings) are all well-defined,
* Correctly resolved identifiers are well-defined,
* A field access expression such as `o.f` is well-defined if the object (`o`) is well-defined and `o != null` (and the expression is well-typed, that is, `f` is a field of the static type of `o`),
* `a.length` is well-defined if `a` is a well-defined array that is not null,
* An array access expression such as `a[i]` is well-defined if the array expression (`a`) and the index expression (`i`) are well-defined, `a` is not null, and `0 <= i < a.length`,
* Unary and binary operator expressions (excluding `&&` and `||` and `==>`)
 are well-defined if: (a) the operands are all well-defined, (b) for division (`/`) and modulo (`%`), the right operand is not zero, (c) the result of the operation is necessarily in range of the result type (depending on the [arithmetic mode](ArithmeticModes)), and (d) for bit-shift operations (`<<`, `>>`, `>>>`), the value of the right operand is non-negative and less than the number of bits in the type of the left operand
* The short-circuiting `&&` is well-defined if the left operand is well-defined and, when the left operand is true, then the right operand is well-defined
* The short-circuiting `||` is well-defined if the left operand is well-defined and, when the left operand is false, then the right operand is well-defined
* a `==>`  expression is well-defined if the left operand is well-defined and,
if the left-operand is true, the right operand is well-defined
* A conditional operator (`p ? q : r`) is well-defined if: (a) the condition (`p`) is well defined and (b) if the condition is true, then the then-expression (`q`) is well-defined and (c) if the condition is false, then the else-expression (`r`) is well-defined
* The `instanceof` expression is well-defined if its left-hand expression is well-defined (the right hand-expression is a type name). Note that the `instanceof` expression is still well-defined if the left-hand expression is `null` (in which case the expression's value will be false).
* A cast operation such as `(T)o` is well-defined if its argument expression (`o`) is well-defined (since the type `T` being cast to is just a type name). (The argument may be `null`, in which case the result of the operation is `null`.)
* A method call expression such as `o.m(es...)` or object creation expression such as `o.new T(...)` is well-defined if the receiver expression (`o`) is either absent or a type name or a well-defined expression and all the arguments (`es...`) are well-defined
* A switch expression (such as `switch (V) { ... }`) is well-defined if the switch value expression (`V`) is well-defined and the selected expression is well-defined. The switch expression is short-circuiting in the sense that any expression for cases that are not selected are not evaluated and so do not need to be well-defined.

JML statements are well-defined if all their component sub-statements and sub-expressions are well-defined. That is, for a statement to be well-defined, each part must be well-defined; the even applies to if, if-else, and switch statements.

As for other JML operations
* singleton JML expression identifiers like `\result` are well-defined expressions (presuming they are type-correct, as always)
* functional-form JML expressions are well-defined if all expression arguments are well-defined; any additional conditions will be stated when the expression is introduced
* a [quantified expression](Expressions#QuantifiedExpressions) (`Q x; R; V`) is well-defined if (a) the range expression (`R`) is well-defined for all values of the local variable (for its type) and (b) the value expression (`V`) is well-defined for each value of the local variable for which in range value is true (and for the `\choose` operation, the corresponding `\exists` expression is true)

In practice, one can make sure that JML expressions are well-defined by writing guarded expressions, such as `o != null ==> o.f == 0`. In that expression, the antecedent (`o != null`) ensures that `o.f` is well-defined, since when `o` is `null`, then the antecedent is false, and so the entire expression is well-defined.

So, since in the example below, since `o` is declared to be non-null (which it would be by default--- see the lesson on [nullness](Nullness)), no definedness errors are issued:
```
{% include_relative T_WellDefined2.java %}
```
But if `o` might be null, as in the following example,
```
{% include_relative T_WellDefined3.java %}
```
then the following messages happen:
```
{% include_relative T_WellDefined3.out %}
```

Finally well-definedness is a requirement for JML expressions, not Java expressions. But similar Java expressions would just throw exceptions, so OpenJML gives slightly different verification messages:
```
{% include_relative T_WellDefined4.java %}
```
gives
```
{% include_relative T_WellDefined4.out %}
```

## **[Well-defined Expressions](https://www.openjml.org/tutorial/exercises/WellDefinedEx.html)**
