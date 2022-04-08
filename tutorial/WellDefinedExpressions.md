---
title: JML Tutorial - Well-Defined Expressions
---

Much confusion over error messages can be avoided by understanding that all JML expressions must be *well-defined*. Informally, one can think of a well-defined expression as one that, if it were a Java expression, would not throw an exception and would have an unambiguous meaning. JML requires that each expression in a JML context must be well-defined; the OpenJML tool will complain if it cannot prove that an expression is well-defined.

For example, `a[i]` is not well-defined if `i` is not in the range of the indices of `a`. So this example

```
// openjml --esc T_WellDefined1.java
public class T_WellDefined1 {

  public void example(int[] a, int i) {
    //@ assert a[i] == 0;
  }
}
```

produces this result

```
T_WellDefined1.java:5: verify: The prover cannot establish an assertion (Assert) in method example
    //@ assert a[i] == 0;
        ^
T_WellDefined1.java:5: verify: The prover cannot establish an assertion (UndefinedNegativeIndex) in method example
    //@ assert a[i] == 0;
                ^
T_WellDefined1.java:5: verify: The prover cannot establish an assertion (UndefinedTooLargeIndex) in method example
    //@ assert a[i] == 0;
                ^
3 verification failures
```

The output here deserves some explanation:
* First, OpenJML will continue looking for errors until it can find no more, but the order in which the errors are found is non-deterministic. So in fact, the output you obtain by running the example above may have the error messages in a different order.
* The tool explores all possible paths in the method, using all possible values of the inputs that conform to the preconditions (an implicit pre-condition here is that `a` is non-null --- we'll deal with that later: [null and non-null defaults](Nullness)).
* Now `a[i]` is well-defined only if `i` is in range for the array `a`. But one possible combination of inputs is that `i` is actually in range, in which case the expression is well-defined and OpenJML goes on to see if the assertion can be proved true. As we know nothing about the values in the array, the assertion cannot be proved true and a verification error message results.
* The other two cases are when `i` is too large (at least as large as `a.length`) or too small (`i` is negative). In these cases the expression is not well-defined; OpenJML issues verification errors calling out this undefinedness.

The rules for well-definedness of an expression build up from the leaves of the expression tree, with any compound expression requiring that each of its sub-expressions be well-defined. Note that even before OpenJML begins its work, an expression must not have any parse or type-checking errors.

* Literals (`true`, `false`, `null`, numbers and literal strings) are all well-defined
* Correctly resolved identifiers are well-defined
* The expression `o.f` is well-defined if `o` is well-defined and `o != null` (and the expression is well-typed, that is, `f` is a field of the static type of `o`)
* `a.length` is well-defined if `a` is well-defined
* `a[i]` is well-defined if expressions `a` and `i` are well-defined and `0 <= i < a.length`
* all unary and binary operator expressions (excluding `&&` and `||` and `==>`,
but including assignment and op-assignment)
 are well-defined if the operands are well-defined and, for division (`/` and `/=`) and modulo (`%` and `%=`), the right operand is not zero
* TODO - what about shift, arithmetic overflow
* the short-circuiting `&&` is well-defined if the left operand is well-defined and, if the left operand is true, the right operand is well-defined
* the short-circuiting `||` is well-defined if the left operand is well-defined and, if the left operand is false, the right operand is well-defined
* a `==>`  expression is well-defined if the left operand is well-defined and,
if the left-operand is true, the right operand is well-defined
* a conditional operator (`p ? q : r`) is well-defined if (a) the condition is well defined and (b) if the condition is true, then the then-expression is well-defined and (c) if the condition is false, then the else-expression is well-defined
* the `instanceof` expression is well-defined if its left-hand expression is well-defined (the right hand-expression is a type name). Note that the `instanceof` expression is still well-defined if the left-hand expression is `null` and its value will be false.
* a cast operation (`(T)o`) is well-defined if its argument expression is well-defined (the type being cast to is just a type name). The argument may be `null`, in which case the result of the operation is `null`.
* a method call expression (`o.m(..)`) or object creation expression (`o.new T(...)`)is well-defined if the receiver expression is either absent or a type name or a well-defined expression and all the arguments are well-defined
* a switch expression is well-defined if the switch value is well-defined and the selected expression is well-defined. The switch expression is short-circuiting in the sense that any expression for cases that are not selected are not evaluated and so do not need to be well-defined.

Java and JML statements are well-defined if all their component sub-statements and sub-expressions are well-defined. There is no-short-circuiting, even if the case of if, if-else, or switch statements.

As for other JML operationas
* singleton JML expression identifiers like `\result` are well-defined expressions (always presuming they are type-correct)
* functional-form JML expressions are well-defined if all expression arguments are well-defined; any additional conditions will be stated when the expression is introduced
* a [quantified expression](QuantifierExpressions) (`Q x; range; value`) is well-defined if (a) the  range expression is well-defined for all values of the local variable (for its type) and (b) the value expression is well-defined for any value of the local variable for which in range value is true


The requirement that JML expressions be well-defined leads to writing guarded expressions, such as `o != null ==> o.f == 0` as `o.f` by itself might be not well-defined. However, `o.f` by itself is well-defined, if it can be proved for the context of that expression that `o != null`.

So, since in this example, `o` is designated as non-null (which it would be by default--- see the lesson on [nullness](Nullness)), no definedness errors are issued:
```
// openjml --esc T_WellDefined2.java
public class T_WellDefined2 {
  int f;
  public void example(/*@ non_null */ T_WellDefined2 o) {
    //@ assert o.f == o.f;
  }
}
```
But if `o` might be null, as in the following example,
```
// openjml --esc T_WellDefined3.java
public class T_WellDefined3 {
  int f;
  public void example(/*@ nullable */ T_WellDefined3 o) {
    //@ assert o.f == o.f;
  }
}
```
then the following messages happen:
```
T_WellDefined3.java:5: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method example
    //@ assert o.f == o.f;
                ^
1 verification failure
```

Finally well-definedness is a requirement for JML expressions, not Java expressions. But similar Java expressions would just throw exceptions, so OpenJML gives slightly different verification messages:
```
// openjml --esc T_WellDefined4.java
public class T_WellDefined4 {
  int f;
  public void example(/*@ nullable */ T_WellDefined4 o) {
    o.f = 0; // a Java statement
  }
}
```
gives
```
T_WellDefined4.java:5: verify: The prover cannot establish an assertion (PossiblyNullDeReference) in method example
    o.f = 0; // a Java statement
     ^
1 verification failure
```


<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>
