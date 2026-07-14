// openjml --esc QuadraticAns.java
public class QuadraticAns {
    /* factors are: (x + first) and (x + second) */
    private /*@ spec_public @*/ double first;
    private /*@ spec_public @*/ double second;

    //@ requires !Double.isNaN(f);
    //@ requires !Double.isNaN(s);
    //@ requires 0.0 < (f+s)*(f+s) - 4.0 * (f*s);
    /*@ ensures first == f && second == s; @*/
    public QuadraticAns(double f, double s) {
        first = f;
        second = s;
    }

    //@ old double epsilon = 0.1e-9;
    //@ old double fps = first+second;
    //@ old double discrim = fps*fps - 4.0 * (first*second);
    //@ requires 0.0 < discrim;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (-fps + Math.sqrt(discrim) / 2.0)) < epsilon;
    //@ ensures Math.abs(\result[1] - (-fps - Math.sqrt(discrim) / 2.0)) < epsilon;
    //@ pure
    public double[] roots() {
        double res[] = new double[2];
        if (second > first) {
            res[0] = -first;
            res[1] = -second;
        } else {
            res[0] = -second;
            res[1] = first;
        }
        return res;
    }
}
