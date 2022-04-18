---
title: JML Tutorial - Invariants
---

JML uses `invariant` clauses to specify properties of an object that should "always" hold. This lesson describes the straightforward uses of invariants
and also the complexities of what "always" means.

## Simple invariants

The basic idea of an invariant is this: an invariant describes a property that always holds of an object. Every method can assume the invariants hold and
must preserve the invariants. Constructors create objects that satisfy invariants. In this sense, invariants are like pre- and postconditions common to every
method and constructor.
* Invariants can be declared `static`, in which case they apply also to static methods. Static invariants apply to all methods; non-static invariants only apply to non-static methods.
* Most typically invariants are declared `public`.  See the discussion below about visibility.

Here is a typical simple example:
```
{% include_relative MyBox.java %}
```

This example shows part of a simple class that has a `size` property. The specification records that this size is always to be a non-negative integer.
So the constructor makes sure that `size` is non-negative when a `MyBox` is created. In `doit()`, `size` is used to create an array. The call of 
`doit`() can assume that the invariants of `this` hold at the beginning of the call; consequently it does not need to check that `size` is non-negative before using its value as the length of the new array.

On the other hand, `shrink()` is intended to make the `MyBox` smaller by reducing its size by 10. It dutifully specifies that it `assigns size;`.
However, a verification attempt reports the following:
```
{% include_relative MyBox.out %}
```
Here `InvariantExit` means that on exit from the method, the invariant cannot be proven --- which is clearly the case if the `MyBox` has a size less than 10 in the pre-state of the `shrink()` method.

## helper methods

Sometimes it is useful or simpler if a method does not need to assume or ensure the invariants. In such a case, the method can be declared a `helper` method.
Consider the difference between `size()` and `sizeH()` in the code listing above.

`size()` is a conventional non-helper getter method. It assumes the invariant holds and returns the value of `size`. A client routine, such as `test1()`, can prove that 
`mybox.size() >= 0` after creating a `MyBox` object. 

`sizeH()` on the other hand is declared `helper`. It does not assume that `size` is non-negative. That does not matter here, but it would, for example if `doit()` were declared helper; in that case `doit()` would need a precondition that required `size >= 0`. `sizeH()` verifies OK, but when one uses it, one cannot be assured that the value of `mybox.sizeH()` is non-negative. Method `test2()` proves OK because, although `sizeH()` does not establish the invariant,
it is `pure` so it does not change `size`, and consequently it is provable that the invariant still holds on exit from `test2()`. In `test3()` on the other hand, the program state has been changed by helper method `changeSizeH` to something that may not satisfy the invariant. It is OK to call `sizeH` because it
is helper and does not require the invariant. But then we don't know that the value of `sizeH()` satisfies the invariant either.

If, as in `test4()`, we call `size()` instead of `sizeH()`, we find that there is a verification error because `size()` expects the invariants to hold 
when in fact they may not.

The cost of not having to have the invariants true on entrance to a method is that they may not be true on exit either, though one can always add them into the pre- and postconditions.

## Visibility of invariants

* Invariants have a visibility (public, private, etc.). Almost always, `public` is the appropriate modifier to use. Invariants with visibility other than public only apply where they can be "seen", just like the modifiers when used for methods.
* Invariants cannot use fields or methods with a visibility more constrained than their own. Conseqeuently, as in this case, a private field will need a `spec_public` declaration. See [the lesson on Visibility](Visibility) for more on this topic.

## Invariants when calling methods

Except in the case of helper methods, methods assume that their invariants are true in their pre-state. Thus when a method is called by some caller method, 
the caller is responsible to be sure that the callee's invariants are true before invoking the callee, just as the caller has to be sure that the callee's
preconditions hold before invoking the callee.

In fact, the callee generally expects that the invariants of all of its formal parameters also hold.

To further complicate matters, JML expects that all invariants of all objects hold at the invocation of a callee, _including those of the caller itself_.
The reason for this rule is shown in this code snippet.
```
public class SomeClass {
  //@ public invariant ...

  public void m(SomeOtherClass o) {
    // some code that temporarily invalidates the invariant of SomeClass
    o.dosomething(this);
    // code that restore the invariant of SomeClass
  }
}
```
The verification attempt of `SomeClass.m` invalidates and then restores the invariant of `SomeClass`. However, `o.dosomething` is called when the invariant
of `this` is invalid. `o.dosomething` might actually call a method of `SomeClass` on its argument, which method would then be called in a state in which
its invariants do not hold. Not knowing what `o.dosomething` does, JML insists on the general rule that all invariants have to hold at every call point.
But this is a nuisance in the implementation of `m`, particularly if `o.dosomething` is a simple library routine like `Math.abs`.

```diff
! Because of this, the rules about invariants holding are a topic of research and discussion. OpenJML is experimenting with more relaxed rules that are still sound.
```
    
