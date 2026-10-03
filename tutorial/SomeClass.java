// openjml --esc SomeClass.java
public class SomeClass {
    private /*@ spec_public @*/ int x;
    //@ public invariant 0 < x;

    public void m(SomeOtherClass o) {
        // code below may temporarily invalidate the invariant
        int oldx = x;
        x = -5; // such as this, which is invalidating the invariant
        o.doSomething(this);  // ERROR: calling a method when invariant broken!
        // code that restores the invariant of SomeClass
        x = oldx; // such as this, restoring SomeClass's invariant
    }
}
