// openjml --esc RationalAns.java
public class RationalAns {
    private /*@ spec_public @*/ long n, d;
    //@ public invariant d != 0;
    //@ public invariant n % d != 0;

    //@ requires dv != 0;
    //@ requires nv % dv != 0;
    public RationalAns(int nv, int dv) {
        n = nv;
        d = dv;
    }

    //@   requires oth == null;
    //@   ensures !\result;
    //@ also
    //@   requires oth != null;
    //@   ensures \result <==> d * oth.n == n * oth.d;
    //@ spec_pure
    public boolean equals(/*@ nullable @*/ RationalAns oth) {
        if (oth == null) {
            return false;
        }
        /*@ assume (n == oth.n && d == oth.d && d != 0 && n%d == 0)
                   <==> (d*oth.n == n*oth.d); @*/
        return n == oth.n && d == oth.d;
    }
        
}
