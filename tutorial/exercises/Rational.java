// openjml --esc Rational.java
public class Rational {
    private /*@ spec_public @*/ long n, d;

    //@ requires dv != 0;
    //@ requires nv % dv != 0;
    public Rational(int nv, int dv) {
        n = nv;
        d = dv;
    }

    //@   requires oth == null;
    //@   ensures !\result;
    //@ also
    //@   requires oth != null;
    //@   ensures \result <==> d * oth.n == n * oth.d;
    //@ spec_pure
    public boolean equals(/*@ nullable @*/ Rational oth) {
        if (oth == null) {
            return false;
        }
        // Why would the following be correct? When would it be correct?
        return n == oth.n && d == oth.d;
    }
        
}
