---
title: JML Tutorial - Exercises - Visibility
---
# Ghost Variable Exercises Key:

## **Question 1**
The following class is one way to do this exercise.

```
public class IntPair {

    private /*@ spec_public @*/ final int lesser, greater;
    private /*@ spec_public @*/ final boolean increasing;

    //@ public ghost final int first;
    //@ public ghost final int second;

    //@ public invariant lesser <= greater;
    //@ public invariant lesser <= first && lesser <= second;
    // the following is a "representation invariant"
    //@ public invariant increasing ==> (first == lesser && second == greater);
    //@ public invariant !increasing ==> (second == lesser && first == greater);

    //@ ensures first == fv && second == sv;
    public IntPair(int fv, int sv) {
        //@ set first = fv;
        //@ set second = sv;
        increasing = (fv <= sv);
        if (increasing) {
            lesser = fv;
            greater = sv;
        } else {
            lesser = sv;
            greater = fv;
        }
   }

    //@ ensures \result <= first && \result <= second;
    //@ spec_pure
    public int lesserValue() {
        return lesser;
    }

    //@ ensures \result == first;
    //@ spec_pure
    public int firstElem() {
        return (increasing ? lesser : greater);
    }
}
```

Note that ghost fields, such as `first` and `second` can be initialized in constructors and must have a visibility declared.  Also the invariants are public, so the private fields must be declared to be `spec_public` so that they can be used in the invariants.

## **Question 2 (Advanced)**

One way to do this exercise is shown below. Note that the model fields are tied to private fields of the class by private represents clauses; JML allows both public and private fields to appear in a private represents clause.

```
public class IntPair {
    //@ public model boolean mincreasing;
    //@ public model int mlesser, mgreater;
    //@ public model int first, second;
    
    private final int lesser; //@ in mlesser;
    private final int greater; //@ in mgreater;
    private final boolean increasing; //@ in mincreasing;

    //@ private represents mincreasing = increasing;
    //@ private represents mlesser = lesser;
    //@ private represents mgreater = greater;
    //@ private represents first = (increasing ? lesser : greater);
    //@ private represents second = (increasing ? greater : lesser);

    //@ public invariant mlesser <= mgreater;
    //@ public invariant mlesser <= first && mlesser <= second;
    //@ public invariant first <= mgreater && second <= mgreater;

    //@ ensures first == fv && second == sv;
    public IntPair(int fv, int sv) {
        increasing = (fv <= sv);
        if (increasing) {
            lesser = fv;
            greater = sv;
        } else {
            lesser = sv;
            greater = fv;
        }
   }

    //@ ensures \result <= first && \result <= second;
    //@ spec_pure
    public int lesserValue() {
        return lesser;
    }

    //@ ensures \result == first;
    //@ spec_pure
    public int firstElem() {
        return (increasing ? lesser : greater);
    }
}
```
