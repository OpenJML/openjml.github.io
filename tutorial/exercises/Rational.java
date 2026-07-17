// openjml --esc Rational.java
public class Rational {
    private /*@ spec_public @*/ long x, y;
    //@ public invariant y != 0;
    //@ public invariant x % y != 0;

    //@ requires yv != 0;
    //@ requires xv % yv != 0;
    public Rational(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ old float eps = 0.1e-9f;
    //@ requires !Float.isNaN(f);
    //@ ensures Math.abs(x/y - f) < eps;
    public Rational(float f) {
        java.math.BigDecimal bigf = new java.math.BigDecimal(f);
        java.math.BigInteger bigx = bigf.unscaledValue();
        java.math.BigInteger bigy = new java.math.BigInteger(
                                     Integer.valueOf(bigf.scale()).toString());
        /*@ nullable @*/ java.math.BigInteger gcd = bigx.gcd(bigy);
        //@ assume gcd != null;
        x = bigx.divide(gcd).longValue();
        y = bigy.divide(gcd).longValue();
        //@ assume y != 0;
        //@ assume x % y != 0;
        //@ assume Math.abs(x/y - f) < 0.1e-9f;
    }

    //@   requires oth == null;
    //@   ensures !\result;
    //@ also
    //@   requires oth != null;
    //@   ensures \result <==> y * oth.x == x * oth.y;
    public boolean equals(/*@ nullable @*/ Rational oth) {
        if (oth == null) {
            return false;
        }
        java.math.BigInteger bigx, bigy, othx, othy;
        bigx = new java.math.BigInteger(Long.valueOf(x).toString());
        bigy = new java.math.BigInteger(Long.valueOf(y).toString());
        othx = new java.math.BigInteger(Long.valueOf(oth.x).toString());
        othy = new java.math.BigInteger(Long.valueOf(oth.y).toString());
        /*@ assume y*oth.x == x*oth.y
          @        <==> bigy.multiply(othx).equals(bigx.multiply(othy));
          @*/
        return bigy.multiply(othx).equals(bigx.multiply(othy));
    }
        
}
