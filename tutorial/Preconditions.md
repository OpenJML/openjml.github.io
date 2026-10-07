---
title: JML Tutorial - Preconditions (requires clauses)
---

## Purpose and Use of Preconditions

Sometimes a method may work (or be well-defined) only for certain combinations of program states and actual arguments.
Such restrictions are called *preconditions* and are written with one (or more) *requires* clause(s).

For example, a method to compute an integer square root requires its
input to be non-negative:
```Java
{% include_relative T_requires1.java %}
```

Other common preconditions are that a collection is not empty
(e.g., `!c.isEmpty()`)
or that an index is in range for an array (`0 <= i < a.length`).
Note that the default in JML is that arguments are automatically considered to be non-null (`a != null`) unless the specification indicates otherwise; see [Null and non-null](Nullness), thus it is not usually necessary to state which arguments are non-null in JML specifications.

A method's specifications may include more than one requires clause. For example, in the following, the two requires clauses must both hold. (Sometimes this separation is useful to isolate what predicate is failing for a particular call.)
```Java
{% include_relative T_requires2.java %}
```

If there are several requires clauses in a method specification, then they are implicitly conjoined with Java's short-circuit `&&` operator.
For example, in the following, the expression `a.length` in
the third clause is undefined if `a` is null. Thus we also need the
condition stated in the third requires clause, and it must be stated before the
second clause. 
```Java
{% include_relative T_requires3.java %}
```

The order shown above results in a verification error (when the arguments are nullable by default).

```Java
{% include_relative T_requires3.out %}
```

## Special Considerations for Floating-Point Numbers and Java's NaN

NaN stands for “not a number” and is used as the result of a floating point operation that results in an undefined answer. A common example of this would be trying to divide zero by zero or taking the square root of a negative number.

It is usually necessary to use the `isNaN()` method from the Java class `Double` (or `Float`) when working with floating point numbers because every other test involving floating point numbers returns _false_ if at least one number is NaN.
(This is even true for `==`; even if `x` and `y` are both NaN, then `x == y` is _false_, so testing arguments with `isNaN()` is the only reliable way to work with floating point numbers.

Therefore, a typical precondition for a method that has floating point numbers as arguments is `!Double.isNaN(arg)`, after which other logical operators and comparisons behave more logically.

## Strength of Predicates and Specifications

In posing exercises (and in simplifying predicates) it is often the logical notion of the strength of predicates and specifications is often useful.
Suppose predicate P implies Q (in JML this would be written `P ==> Q`);
then P is _stronger than_ Q, so Q is _weaker than_ P.
For example, `x > 1` implies `x > 0`, so `x > 1` is stronger than `x > 0`.
So the _strongest predicate_ is one that implies all others, which is the predicate `false`.

Although in JML one can add many clauses to specifications, what we call a
_simple specification_ has just a single precondition and a single postcondition.
We write _(P,Q)_ for a simple specification with precondition _P_ and postcondition _Q_.

A simple specification _(P,Q)_ is _stronger than_ _(P',Q')_ when every correct implementation of _(P,Q)_ is also correct for _(P',Q')_. Thus, _(P,Q)_ is _stronger than_ _(P',Q')_ when _P'_ is stronger than _P_ and _Q_ is stronger than _Q'_, so the stronger specification works in at least as many cases (as it has a weaker precondition), 
but will always finish in a state that satisfies the postcondition of the weaker specification.
In the literature, it is often said that _(P,Q)_ _refines_ _(P',Q')_
when _(P,Q)_ is stronger than _(P',Q')_.
Thus the strongest specification is also the _most refined_ specification and permits no more correct implementations than the specifications it refines.

## **[Exercises](https://www.openjml.org/tutorial/exercises/PreCondEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_requires1 file](T_requires1.java)
+ [T_requires2 file](T_requires2.java)
+ [T_requires3 file](T_requires3.java)
