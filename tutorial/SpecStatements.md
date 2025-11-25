---
title: Specifications in Method Bodies
---

The basic unit of specification and verification in JML is the method,
with the method body being compared to the method's specification.
However, sometimes specifications within the body of a method can
assist or are required to be able to prove that the body meets the
method specification.

The most common such specification statements are `assert`, `assume`,
and `ghost` declaration statements. In addition, loops in a method
body require a loop specification to be able to reason about the
effect of that method body.s
