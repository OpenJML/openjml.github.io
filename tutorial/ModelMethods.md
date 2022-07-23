---
title: JML Tutorial - Model methods
---

The [previous lesson](ModelFields) described how to use model fields to specify an abstraction. Sometimes model methods can be used instead, though when
model fields are applicable they generally are easier to use in specifications and easier to prove. This lesson alters the example of the previous lesson
to use methods instead.

At the outset, note that methods used in specifications must be `pure` ([cf. here](MethodsInSpecifications)), but can be either Java methods or JML methods. One uses
a JML method if there is no Java method that accomplishes what is needed. A JML model method is declared just like a Java method except that
* it is written in a JML annotation
* it includes the `model` modifier
* it need not have an implementation (and generally does not, except if compilation for runtime-assertion-checking is desired).

For example, if the example below did not declare `sides()` as a Java method, one could include in `Polygon3` this declaration, along with any specifications:
```
//@ model public int sides();
```

## using model methods

Here is the [model field example](ModelFields), altered to use methods --- in this case the Java methods already part of the `Polygon` interface. There are a few key points to note:
* The datagroup is still needed. When using model methods, one typically will declare standalone datagroups to use in frame conditions.
* Reads clauses are needed. They are discussed after the code listing.
* If the methods are used within invariants, they typically need to be declared `helper` and that they do not throw exceptions (`public normal_behavior`).
* An abstract method used in modeling typically has no postcondition, or at least not one that fully dictates its value. It is used as an
_uninterpreted function_, whose value is given by invariants and concrete implementations and the pre- and postconditions in which it is used.

```
{% include_relative Polygon3.java %}
```

## reads clauses

When specifying a method like `twice()` that modifies the program state, it is the frame condition (the `assigns` clause) that tells what part of the program state is modified. Any particular (model) field or array element can be checked to see if it is part of the changed state. If not, the verification system knows that
that field was not changed by the method call.

The example code above uses model methods instead of model fields. So in the `test()` routine, how is it known that `polygon.sides()` does not change
value upon the call of `twice()` and that `polygon.longestSide()` does change? The answer is the `reads` clause; this clause states what fields a method
_reads_ or _depends on_. The content of the reads clause may be a model field.

Note that `twice()` assigns to `allSides` and `longestSide()` reads `allSides`. So the value of `longestSide()` might well be changed by the call of `twice()` (though not necessarily).
But `sides()` reads the model field `numSides`, which is not assigned by `twice()`, so its value does not change.

## helper methods

A _helper_ method is one that does not assume that the object's invariants hold (cf. [the lesson on invariants](Invariants)), nor does it 
ensure that they hold after returning. Methods used in invariant clauses need to be `helper` methods because otherwise there would be 
unending recursive calls to check if the invariants are all true. The disadvantage of being a helper method is that sometimes additional pre- or postconditions are needed to assume or assert properties that are otherwise part of the object's invariants.
