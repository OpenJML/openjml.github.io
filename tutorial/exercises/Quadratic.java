// openjml --esc --timeout=60 Quadratic.java
public class Quadratic {
    /** This class represents the quadratic formula
        first*x^2 + second*x + third **/
    private /*@ spec_public @*/ double first;
    private /*@ spec_public @*/ double second;
    private /*@ spec_public @*/ double third;

    //@ requires !Double.isNaN(a);
    //@ requires !Double.isNaN(b);
    //@ requires !Double.isNaN(c);
    //@ requires 0.0 < a < Double.POSITIVE_INFINITY;
    //@ requires 0.0 < (b*b) - 4.0 * (a*c) < Double.POSITIVE_INFINITY;
    /*@ ensures first == a && second == b && third == c; @*/
    public Quadratic(double a, double b, double c) {
        first = a;
        second = b;
        third = c;
    }

    //@ requires 0.0 < (second*second) - 4.0*first*third < Double.POSITIVE_INFINITY;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - ((-second + Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;

    //@ ensures Math.abs(\result[1] - ((-second - Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
    //@ pure
    public double[] roots() {
        //@ assume 0.0 < first < Double.POSITIVE_INFINITY;
        //@ assume second != Double.POSITIVE_INFINITY;
        //@ assume second != Double.NEGATIVE_INFINITY;
        //@ assume third != Double.POSITIVE_INFINITY;
        //@ assume third != Double.NEGATIVE_INFINITY;
        double res[] = new double[2];
        res[0] = -second + Math.sqrt((second*second) - 4.0*first*third) / (2.0*first);
        //@ assume Math.abs(res[0] - ((-second + Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
        res[1] = -second - Math.sqrt((second*second) - 4.0*first*third) / (2.0*first);
        //@ assume Math.abs(res[1] - ((-second - Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
        return res;
    }
}
