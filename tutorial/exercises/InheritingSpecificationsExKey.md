---
title: JML Tutorial - Exercises - Inheriting Specifications
---
# Inheriting Specifications Exercises:
## [Inheriting Specifications Tutorial](https://www.openjml.org/tutorial/InheritingSpecifications)

## **Question 1**

a. Yes, in JML all subclasses are automatically behavioral subtypes. However, note that `PositivePoint` cannot be correctly implemented with these added invariants, due to the impossibility of implementing the `setX` and `setY` methods correctly.

b. No, these inherited implementations of `setX` and `setY` are not correct, since they may be used with the specification given in `Point`, which allows a negative number to be used as an argument, which would violate the invariants of `PositivePoint`. If one tries to add preconditions to these methods (requiring that the argument be positive) as another specification case for such a method, then the problem is that in JML such preconditions are disjoined (with `||`) to the existing precondition, showing that clients that use those methods may continue to use them as if the receivers were points. However, since the specification case inherited from `Point` allows a negative argument for these methods, and ensures that such an argument becomes the new coordinate, it is impossible to correctly implement such a method. This shows that one must plan ahead for subtyping in such cases (e.g., by allowing an exception to be thrown in the specification of the supertype).

c. Java code that would demonstrate the problem is as follows.

```
        PositivePoint pp = new PositivePoint(3,4);
        pp.setX(-3);
```

The call `pp.setX(-3)` satisfies the precondition specified for `setX` in `Point`, but either the postcondition of that specification (for `setX` in `Point`) or the (first) invariant in `PositivePoint` must be violated in the code for `setX`.

## **Question 2**
One solution to this exercise is as follows. Since the `setAge` method is an added method, its specification does not need to start with `also`. However, this interface inherits the model field `age` from the super-interface `Age`. This solution uses `normal_behavior` to emphasize that when the precondition is true, no exception can be thrown. This behavior is implicitly `public` because the method is public (and the specification is also in an interface).

```
public interface NormalSetAge extends Age {
    /*@ normal_behavior
      @   requires 0 <= a && age <= a <= 150;
      @   assignable age;
      @   ensures age == a;    @*/
    public void setAge(int a);
}
```

## **Question 3**
One solution to this exercise is as follows, which leaves the inherited model field `age` unchanged upon receiving an argument that is (strictly) less than the value of `age`.

```
public interface ExceptionalSetAge extends Age {
    /*@ exceptional_behavior
      @   requires a < age;
      @   assignable \nothing;
      @   signals_only IllegalArgumentException;
      @*/
    void setAge(int a); 
}
```

## **Question 4**
One solution to this is as follows.  

```
public interface Gendered {
    //@ model instance String gender;

    //@ ensures \result == gender.equals("female");
    /*@ spec_pure @*/ boolean isFemale();
}
```

As the exercise states, the model instance field `gender` is a `String`. This allows the gender to be `"female"`, or other genders such as `"male"` (or for nouns in gendered languages, something like `"neuter"`).

The method `isFemale()` is `spec_pure` which allows it to be used in specifications (e.g., during runtime assertion checking). See [the discussion about pure methods in the tutorial about method specifications](https://openjml.org/tutorial/MethodsInSpecifications) for more about this topic.

## **Question 5**
One solution is the following class.

```
public class Human extends Animal {
    //@ public model boolean discount; //@ in age;
    protected boolean _discount = false; //@ in discount;
    //@ protected represents discount = _discount;

    /*@ also
      @   requires age <= a && 65 <= a && a <= 150;
      @   assignable age;
      @   ensures discount;   @*/
    public void setAge(int a) {
	super.setAge(a);
 	if (65 <= a) { _discount = true; }
    }

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    public Human(String g) {
        super(g);
    }
}
```

Note how the protected model field is represented using a protected represents clause. Also note that the additional specification case for the method `setAge` begins with `also` and makes a super call to the superclass's `setAge` method. When that super call throws an exception, then the code given will pass along the exception to the caller of the method.

## **Question 6**
One solution is the following class.

```
public class Human extends Animal {
    //@ public model boolean discount; //@ in age;
    protected boolean _discount = false; //@ in discount;
    //@ protected represents discount = _discount;

    /*@ also
      @   requires age <= a && 65 <= a && a <= 150;
      @   assignable age;
      @   ensures discount;   @*/
    public void setAge(int a) {
	super.setAge(a);
 	if (65 <= a) { _discount = true; }
    }

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    public Human(String g) {
        super(g);
    }
}
```

This exercise shows that a subtype may add additional fields to a datagroup, in this case the model field `discount` was added to the datagroup `age`. In addition, each model field names a datagroup, and so the concrete field, `_discount` that represents that model field must be added to that datagroup, as `_discount` is added to the datagroup `discount`, which makes it implicitly part of the datagroup `age`, and so `_discount` becomes assignable in the `setAge` method.

## **Question 7**
One solution is as follows.

```
public class Tortoise extends Animal {
    protected int _age; //@ in age;
    //@ protected represents age = _age;

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g) && age == 0;
    public Tortoise(String g) {
        super(g);
        _age = 0;
    }
    
    /*@ also
      @   requires age <= a && 151<=a && a<=400;    
      @   assignable age;
      @   ensures age == a;          @*/
    public void setAge(int a)
    {
        if (a < _age) { throw new IllegalArgumentException(); }
        _age = a;
    }
}
```

This exercise shows that preconditions can be further weakened in a subtype, as is done in the `setAge` method. Note that the added specification case for `setAge` still does not preclude older animals, nor does the code.

Note that the method setAge cannot simply be inherited, because the precondition of the method `setAge` in the class `Animal` has a different precondition, and that precondition must be weakened in the implementation in `Tortoise`.

## **Question 8**
One way to specify an interface like `Gendered` but with an `equals` method that allows for other attributes (aside from the gender) to be taken into account is to say that when the genders are differnt, then the `equals` method must return false. This has the advantage of allowing other attributes of an object to be considered, while requiring comparison of the genders.  This is shown in the following.

```
public interface GenderedWithEquals {
    //@ model instance String gender;

    //@ ensures \result == gender.equals("female");
    /*@ spec_pure @*/ boolean isFemale();

    /*@ also
      @    ensures (obj instanceof GenderedWithEquals)
      @             ==> (!gender.equals(((GenderedWithEquals)obj).gender)
      @                   ==> !\result);
      @*/
    public /*@ pure @*/ 
    boolean equals(/*@ nullable @*/ Object obj);
}
```

Note that, in Java, the `equals` method takes a possibly null `Object` argument. The specification ensures that when the argument has the type `GenderedWithEquals`, then it returns false when the genders are not equal.
However, this cannot be strengthened to say that when the genders are equal, then the method must return `true`, because doing that would prohibit considering other attributes, such as the object's age.

Also recall that Java's `instanceof` operator returns false if its left-hand argument is null. Thus, when `obj instanceof GenderedWithEquals` is true, we know that `obj` must not be null, and so a cast will work.

## **Question 9**
One solution is the following.

```
public interface ExceptionalSetAge2 extends Age {
    /*@ normal_behavior
      @   requires a < age;
      @   assignable \nothing;
      @   ensures \old(age) == age; @*/
    void setAge(int a); 
}
```

## **Question 10**
A class that is similar to `Animal`, called `Animal2` below, inherits from the aabove interface `ExceptionalSetAge2`. Notice that in the implementation of `setAge` obeys both specifications of the method `setAge`.

```
public class Animal2 implements Gendered,
           NormalSetAge, ExceptionalSetAge2 {
    protected boolean _gen; //@ in gender;
    /*@ protected represents gender
      @           = (_gen ? "female" : "male"); 
      @*/

    protected int _age = 0; //@ in age;
    //@ protected represents age = _age;
    
    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g) && age == 0;
    public Animal2(String g) 
    { _gen = g.equals("female"); }

    public /*@ spec_pure @*/ boolean isFemale() 
    { return _gen; }

    public void setAge(int a) {
        if (a < _age) { return; }
        if (_age <= a && a <= 150) { _age = a; }
    }
}

A class like `Human` that inherits from the `Animal2` class above is the following.

```
public class Human2 extends Animal2 {
    //@ public model boolean discount; //@ in age;
    protected boolean _discount = false; //@ in discount;
    //@ protected represents discount = _discount;

    /*@ also
      @   requires age <= a && 65 <= a && a <= 150;
      @   assignable age;
      @   ensures discount;   @*/
    public void setAge(int a) {
        if (a < _age) { return; }
	super.setAge(a);
 	if (65 <= a) { _discount = true; }
    }

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    public Human2(String g) {
        super(g);
    }
}
```
