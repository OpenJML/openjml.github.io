---
title: JML Tutorial - Model methods
---

The [previous lesson](ModelFields) described how to use model fields to specify an abstraction. Sometimes model methods can be used instead, though when
model fields are applicable they generally are easier to use in specifications and easier to prove. This lesson alters the example of the previous lesson
to use methods instead.

At the outset, note that methods used in specifications must be [`pure`](MethodsInSpecifications), but can be either Java methods or JML methods. One uses
a JML method if there is no Java method that accomplishes what is needed. A JML model method is declared just like a Java method except that
* it is written in a JML annotation
* it includes the `model` modifier
* it need not have an implementation (and generally does not, except if compilation for runtime-assertion-checking is desired).

Here is the previous example, altered to use methods --- in this case the Java methods already part of the `Polygon` interface. There are a few key points to note:
* The datagroup is still needed. When using model methods, one typically will declare standalone datagroups to use in frame conditions.
* Reads clauses are needed. They are discussed after the code listing.
* If the methods are used within invariants, they typically need to be declared `helper` and that they do not throw exceptions (`public normal_behavior`).
* The abstract methods used in modeling typically have no postcondition, or at least not one that fully dictates their value. They are used as
_uninterpreted functions-, whose values is given by invariants and concrete implementations.

```
{% include_relative Polygon3.java %}
```

## reads clauses

When specifying a method like `twice()` that modifies the program state, it is the frame condition (the `assigns` clause) that tells what part of the program state is modified. Any particular (model) field or array element can be checked to see if it is part of the changed state. If not, the verification system knows that
that field was not changed by the method call.

The example code above uses model methods instead of model fields. So in the `test()` routine, how is it know that `polygon.sides()` does not change
value upon the call of `twice()` and that `polygon.longestSide()` does change? The answwer is the `reads` clause; this clause states what fields a method
_reads_ or _depends on_. The content of the reads clause may be a model field.

Note that `twice()` assigns to `allSides` and `longestSide()` reads `allSides`. So the value of `longestSide()` might well change (though not necessarily).
But `sides()` reads the model field `numSides`, which is not assigned by `twice()`, so its value does not change.
