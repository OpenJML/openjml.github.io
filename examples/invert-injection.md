---
layout: default
title: InvertInjection | Examples | OpenJML
---

# OpenJML Examples: Invert Injection

Given an array a that records an injective function 0..N-1 -> 0..M-1,
compute the inverse b from 0..M-1 -> 0..N-1.

Prove that b[a[]i]] == i and a[b[j]] == j.

The challenge in this exercise is to identify the preconditions that 
clarify the problem.

```java
{% include_relative InvertInjection.java %}
```

