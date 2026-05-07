---
title: JML Tutorial - JML Expressions
---

The earlier lessons on pre- and post-conditions, assert and assume
statements all showed examples of *expressions* used in JML clauses.
As expressions are a building block for nearly all other JML constructs, 
we include a couple lessons at this point to introduce JML expressions.

JML expressions look very much  like Java expressions.
Indeed, the JML expression syntax includes all of the Java expression
syntax, with this exception: JML expressions are not allowed to have
side-effects. So the `++`, `--`, and _op_`=` (e.g., `+=`) operators are
not allowed in JML expressions. The meaning of Java operators in 
JML is also unchanged, except for two matters discussed in later lessons:
* consideration of [arithmetic modes](ArithmeticModes)
* [well-definedness](WellDefinedExpressions)

Note that the non-short-circuiting boolean operators `&` and `|` are legal
in both Java and JML, though the short-circuiting versions `&&` and `||`
are much more commonly used in Java because they can be more efficient. In
static reasoning, however, execution efficiency does not matter. 
In static reasoning, `&` and `|` are simpler to reason about, but 
`&&` and `||` are often needed because of [well-definedness considerations](WellDefinedExpressions).

But JML also adds to Java some new operators and expression syntax. The new operators are these:

* `==>` (implication): this binary operator takes two boolean operands, e.g., `p` and `q`; `p ==> q` is read as "p implies q" and means the same as logical implication, that is, the same as "not p or q". 
The implication operator is short-circuiting. That is, the value and well-definedness of the right-hand-side is immaterial, unless the left-hand-side is true. In other words, `p ==> q` is precisely equivalent to `!p || q`.
The implication operator has lower 
precedence than `&&` and `||`, so `p && q ==> r || s` means
`(p && q) ==> (r || s)`. `==>` is *right* associative, so that
`p ==> q ==> r` means `p ==> (q ==> r)`, which is the same as `(p && q) ==> r`.
* `<==>` (equivalence): this is also a binary operation between boolean values.
`p <==> q` means the same as `p == q`, except that `<==>` has lower precedence than `&&` and `||`, whereas `==` has higher precedence. 
Thus `p && q == r || s` means `(p && (q == r)) || s`, whereas
`p && q <==> r || s` means `(p && q) <==> (r || s)`.
Also `<==>` is left associative, so `p <==> q <==>r` means `(p <==> q) <==> r`), 
though (a) the meaning is the same as if it were right associative and (b) 
expressions that rely on associativity of `<==>` may be confusing and so perhaps should be avoided.
* `<=!=>` (inequivalence): this operator is simply the negation of `<==>`
and has the same precedence as `<==>`.  `<=!=>` is left associative:
`p <=!=> q <==> r` is `(p <=!=> q) <==> r`, though again, expressions relying on associativity of `<=!=>` and `<==>` tend to be confusing and so perhaps should be avoided.

Another important addition to JML is the *chaining* of relational operators.
That is, instead of writing `i <= j && j < k`,
one can write `i <= j < k`.
Similarly, `i > j > k` means `i > j & j > k`.
`<` and `<=` can be chained together and `>` and`>=` can be chained together,
but the two groups cannot be mixed.
Furthermore, `==` does not chain and in fact has a lower precedence than the 
relational operators: `a < b == c < d` means `(a < b) == (c < d)` in both Java and JML. These chained operations are particularly convenient for writing
ranges of indices. For example, for an array `a` one might constrain an index variable `i` as `0 <= i < a.length`.

In addition quantified expressions are described below and two other advanced operators are presented in Advanced topics lessons:
* `<:` [Reasoning about types](TYPE)
* `<#` `<#=` [Reasoning about locks](Locks)

Finally, there are many keywords that designate either singleton values (e.g. `\result`) or function-like operations (e.g., `\typeof(...)`. These will be 
explained as needed in future lessons, although one, `\result`, you have already seen. All JML keywords used within expressions begin with a backslash, so they
cannot conflict with Java identifiers.

For example the expression `0 <= \result < a.length` says that the result of the method (`\result`) is a legal index into the array `a`.

Of course, these JML operators and functions (and all other JML syntax) can only be used within JML annotations, not in Java code.

## Quantified expressions {#QuantifiedExpressions}

A general point about all these quantified expressions is that any numeric subexpressions are evaluated in [bigint-math mode](ArithmeticModes) so that there is no concern about overflow in evaluating the expression. Furthermore, arithmetic mode operators (that change the mode of a subexpression) are not allowed within a quantified expression. On the other hand, the result of a quantified expression may be cast to a desired type, since that cast will operate when the expression's computation is complete.

### forall and exists

Quantified expressions are common in logic and are just as necessary in JML to express properties over collections of objects.
The two most common expressions are universal and existential quantification. Here are some common examples:
* `(\forall int i; 0 <= i < a.length; a[i] == 2*i)`
* `(\exists int i; 0 <= i < a.length; a[i] == 0)`

The first expression states the property that _each_ (that is, _all_) of the elements of array `a` have a value equal to twice that element's index. 
The second states that for _some_ index within the array, the value at that index equals 0. Both of these expressions have the same general form: the keyword, a variable declaration (which is local to the expression), a boolean range predicate `R`, and a boolean value predicate `V`. The meaning of the range expression `R` in these forms is as if the quantifier had been written as shown below:
* `(\forall ...; R; V)` is the same as `(\forall ...;; R ==> V)`
* `(\exists ...; R; V)` is the same as `(exists ...;; R && V)`

However separating `R` and `V` makes it easier to have an efficient implementation for runtime-assertion-checking. Note that if the range predicate is false (for example if the array `a` has length 0 in `(\forall int i; 0 <= i < a.length; V)`, then, as in logic, a forall expression will be true, but the exists expression `(\forall int i; 0 <= i < a.length; V)` will be false.

Although it is good practice, and avoids possible confusion about the scope of the declared variable, JML's syntax does not require one to use parentheses around quantified expressions. Without parentheses, the scope of the declared variable extends as far to the right as possible.

These expressions are very commonly used in reasoning about loops, arrays, sequences and sets. For example, to say that every element of a set `s` (where the elements have type `T`) has the property `P` one could write the following expression: `(\forall T e; e \in s; P(e))`.

### choose

The `\choose` predicate is similar to the `\exists` predicate. Whereas `(\exists ...\; R; V)` is true if there is some index for which `R && V` is true,
`\choose` can return that value (as the value of the expression). For example, the value of `(\choose int i; 0 <= i < a.length; a[i] == 0)` is an `int` for which the range and predicate are true, that is in this example, for which the array element is 0. The type of the expression is always the type of the declaration of the declared local variable, as that quantified variable's value is returned as the value of the expression when the predicate (`a[i] == 0` in this example) is true.

If there is more than one such value (in our example more than one such index), the result of the expression might be any one of them, but it will always the same one for a semantically identical expression.
But the fact that the value could be any one satisfying the predicate means that an assertion that uses that value must hold for all cases in which the predicate is true. For example in the expression `P(\choose int i; 0 <= i < a.length; a[i] == 0)`, the value of the overall expression should not depend on the value chosen for `i`.

If `R && V` is false, that is there is no such index, then the expression is not [well-defined](WellDefinedExpressions). Thus, to make sure that a `\choose` predicate is always well-defined, one should make sure that the conjunction of the range expression and the value expression (i.e., `R && V`) is never false.
 
### max and min

The `\max` and `\min` predicates have the same form except that the value term must be numeric, so that the concepts of "maximum" and "minimum" are meaningful. You might ask, for example, for the maximum and minimum values of an array:
* `(\max int i; 0 <= i < a.length; a[i])`
* `(\min int i; 0 <= i < a.length; a[i])`

A first point to note is that these are each equivalent to a choose expression with a pair of forall and exists subexpressions inside.
That is, `x == (\max ...; R; v)` where `x` has a numeric type `T`,
is equivalent to 
`(\choose T v; (\forall ... ; R; x <= v) && (\exists ... ; R; x == v); v)`. That is, the value of the `\max` expression is a number that is at least as large as all the elements being considered and is equal to at least one of them. Similarly, the value of `x == (\min ...; R; v)` is equivalent to
`(\choose T v; (\forall ... ; R; v <= x) && (\exists ... ; R; x == v); v)`, where `T` is again the type of `x`. That is, the value of the `\min` expression is a number that is no bigger than all the elements being considered and is equal to at least one of them.

A second point is that these expressions are not well-defined if the range is empty (that is, when the range predicate is false). 

A third point is that the type of the expression is the same as the type of the value term. However the value term itself is evaluated in bigint-math mode
and only when the max or min has been determined is the result cast back to the final type.

### sum and product

The `\sum` and `\product` quantifiers add up or multiply together all the values of the value term for which the range term is true. For example, the sum or product of all the elements in an array `a` would be expressed as
* `(\sum int i; 0 <= i < a.length; a[i])`
* `(\product int i; 0 <= i < a.length; a[i])`

The type of these operations is `\bigint` simply because overflow is a distinct possibility. The result can always be cast to a desired final type, at which point the final value is checked that it is actually in range for the desired type.

If the range predicate is empty (i.e., false) then the sum is 0 and the product is 1. So these expressions are well-defined even when the range predicate is empty.

The implementation of these two expressions in JML tools is in progress. Don't count on them working yet.

### num_of

A final quantified expression is `\num_of` which counts the number of times the boolean value term is true when the range term is also true. For example,
`(\numof int i; 0 <= i < a.length; a[i] == 0)` counts the number of elements of the array `a` that are 0. Quite obviously
`(\num_of ...; R; V)` is equivalent to `(\sum ... ; R && V; 1)`. The type of a `\num_of` expression is `\bigint` and it can be cast to a desired final type; if the range is empty the value of the expression is 0.

The implementation of this expression in JML tools is in progress. Don't count on it working yet.

TODO - what about \let

## **[JML Expressions Problem Set](https://www.openjml.org/tutorial/exercises/JmlExprEx.html)**


