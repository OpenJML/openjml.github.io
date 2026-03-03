---
title: JML Tutorial - Method Specifications: old clauses and clause ordering
---

We have introduced a few kinds of method specification clauses so far. In fact there are many more, though most are not widely used:
* Precondition clauses
  * [`recommends`](Recommends)
  * [`requires`](Preconditions)
  * [`old`](#old-clause)
* Frame conditions
  * `reads` (`accessible`)
  * [`assignable` (`assigns`, `writes`)](FrameConditions)
  * `captures`
  * `callable`
* Postconditions
  * [`ensures`](Postconditions)
  * [`signals`](SpecifyingExceptions)
  * [`signals_only`](SpecifyingExceptions)
  * `diverges`
  * `duration`
  * `working_space`
* Termination
  * `measured_by`

Some of these have been already discussed; others are discussed in later lessons; and others are omitted from the tutorial because they are too advanced or too ill-defined -- see the JML Reference Manual for details on those. The `old` clause is presented below. Those clauses discussed in this tutorial are clickable hyperlinks in the above list.

## Ordering of clauses

There is no pre-defined order to the clauses within a single specification case (cf. a later lesson on [multiple specification cases](MultipleBehaviors)].
However, a specification is much more readable if the clauses generally follow the order above, with preconditions first, then frame conditions, followed by postconditions.

There is some meaning to the ordering within the precondition group and within the postcondition group: earlier clauses can set conditions that are needed for later clauses to be well-defined; but ordering only matters within the each kinds of clause; that is ordering matters within the set of precondition clauses and separately for any `ensures` clauses. For example,
```
{% include_relative T_order1.java %}
```
yields
```
{% include_relative T_order1.out %}
```
The first requires clause might not be well-defined because `a` might be null. If we reverse the order of the clauses, as in the following specification, then the method verifies:
```
{% include_relative T_order2.java %}
```
is successfully verified.



## old clause

The `old` clause is a means to compute a value (in the pre-state) that is used elsewhere in the specification.
It is a means to factor out common subexpressions, to compute something in the pre-state that is used in the postconditions, or to simply make the specification more readable.
Here is a simple use of it:
```
{% include_relative T_Old.java %}
```

## **[Method Specifications Problem Set](https://www.openjml.org/tutorial/exercises/MethodSpecificationsEx.html)**

