// openjml --esc Quadratic.java
public class Quadratic {
    /* factors are: (x + first) and (x + second) */
    private /*@ spec_public @*/ double first;
    private /*@ spec_public @*/ double second;

    //@ requires !Double.isNaN(f);
    //@ requires !Double.isNaN(s);
    //@ requires 0.0 < (f+s)*(f+s) - 4.0 * (f*s);
    /*@ ensures first == f && second == s; @*/
    public Quadratic(double f, double s) {
        first = f;
        second = s;
    }

    //@ requires 0.0 < (first+second)*(first+second) - 4.0 * (first*second);
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (- (first+second) + Math.sqrt((first+second)*(first+second) - 4.0 * (first*second))) / 2.0) < 0.1e-9;
    //@ ensures Math.abs(\result[1] - (- (first+second) - Math.sqrt((first+second)*(first+second) - 4.0 * (first*second))) / 2.0) < 0.1e-9;
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
