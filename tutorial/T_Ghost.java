// openjml --esc T_Ghost.java
public class T_Ghost {

    private /*@ spec_public @*/ int a = -1;
    private /*@ spec_public @*/ int b = -1;
    //@ public ghost int mean;

    // once the object exists the values of a and b are non-negative
    //@ public invariant (0 <= a && 0 <= b);
    //@ public invariant a+b <= Integer.MAX_VALUE;
    //@ public invariant (mean == (a+b)/2);

    //@ requires 0 <= av && 0 <= bv && av+bv <= Integer.MAX_VALUE;
    //@ ensures a == av && b == bv;
    //@ ensures mean == (a+b)/2;
    public T_Ghost(int av, int bv) {
        a = av;
        b = bv;
        //@ set mean = (a+b)/2;
    }

    //@ ensures \result == mean;
    public int average() {
        return (a+b)/2;
    }
}
