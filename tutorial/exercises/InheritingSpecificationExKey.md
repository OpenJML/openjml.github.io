---
title: JML Tutorial - Exercises - Inheriting Specifications
---
# Inheriting Specifications Exercises:
## [Inheriting Specifications Tutorial](https://www.openjml.org/tutorial/InheritingSpecifications)

## **Question 1**
One solution to this exercise is as follows. Since the `setAge` method is an added method, its specification does not need to start with `also`. However, this interface inherits the model field `age` from the superinterface `Age`.

```
public interface NormalSetAge extends Age {
    /*@  requires 0 <= a && a <= 150;
      @  assignable age;
      @  ensures age == a;    @*/
    public void setAge(int a);
}
```

## **Question 2**
One solution to this exercise is as follows, which leaves the inherited model field `age` unchanged upon receiving an argument that is (strictly) less than the value of `age`.

```
public interface ExceptionalSetAge extends Age {
    /*@   requires a < age;
      @   assignable age;
      @   ensures \old(age) == age; @*/
    void setAge(int a); 
}
```

There is a reason we wanted to have `age` be assignable. First, the default assignable clause for a method is `assignable \everything`, which is too broad to be useful as a method specification. But more importantly, if we used `assignable \nothing` then when combined with the specification in `NormalSetAge` JML would take the intersection of nothing (i.e., the empty set of locations) and the datagroup `age`, which is again the empty set, so the combination would not be allowed to assign to any field, even in the case where the normal precondition is satisfied. On the other hand, when allowing `age` to be assigned, one must prevent it from being changed in the exceptional case, so the postcondition used is `\old(age) == age`, which prohibits the value of that field from changing in that case. Thus the assignable clause, which allows the model field `age` to be changed, allows us to plan for (one or more types that are) subtypes of _both_ interfaces.

**Learning Objectives:**
+ Understand what behavioral subtyping is.
+ Understand how inheritance of specification works.
+ Understand pitfalls of specification inheriance.


