---
title: JML Tutorial - Exercises - Inheriting Specifications
---
# Inheriting Specifications Exercises:
## [Inheriting Specifications Tutorial](https://www.openjml.org/tutorial/InheritingSpecifications)

## **Question 1**
One solution to this exercise is as follows. Since the `setAge` method is an added method, its specification does not need to start with `also`. However, this interface inherits the model field `age` from the super-interface `Age`.

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

## **Question 3**
One solution to this is as follows.  

```
public interface Gendered {
    //@ model instance String gender;

    //@ ensures \result == gender.equals("female");
    /*@ spec_pure @*/ boolean isFemale();
}
```

As the exercise states, the model instance field `gender` is a `String`. This allows the gender to be `"female"`, or other genders such as `"male"` (or for nouns in gendered languages, something like `"neuter"`).

The method `isFemale()` is `spec_pure` which allows it to be used in specifications (e.g., during runtime assertion checking). See [the discussion about pure methods in the tutorial about method specifications for details](https://openjml.org/tutorial/MethodsInSpecifications).


