// openjml --esc --timeout=60 QuadraticAns.java
public class QuadraticAns {
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
    public QuadraticAns(double a, double b, double c) {
        first = a;
        second = b;
        third = c;
    }

    //@ old double eps = 2E-6;
    //@ old double a = first;
    //@ old double b = second;
    //@ old double c = third;
    //@ old double b2 = b*b;
    //@ old double discrim = b2 - 4.0*a*c;
    //@ requires 0.0 < discrim < Double.POSITIVE_INFINITY;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (-b + Math.sqrt(discrim)) / (2.0*a)) < eps;
    //@ ensures Math.abs(\result[1] - (-b - Math.sqrt(discrim)) / (2.0*a)) < eps;
    //@ pure
    public double[] roots() {
        //@ assume 0.0 < first < Double.POSITIVE_INFINITY;
        //@ assume second != Double.POSITIVE_INFINITY;
        //@ assume second != Double.NEGATIVE_INFINITY;
        //@ assume third != Double.POSITIVE_INFINITY;
        //@ assume third != Double.NEGATIVE_INFINITY;
        double eps = 2E-6;
        double a = first;
        double b = second;
        double c = third;
        double b2 = b*b;
        double discrim = b2 - 4.0*a*c;
        //@ assume 0.0 < discrim < Double.POSITIVE_INFINITY;

        double res[] = new double[2];
        res[0] = -b + Math.sqrt(-b + Math.sqrt(discrim) / (2.0*a));
        //@ assume Math.abs(res[0] - (-b + Math.sqrt(discrim)) / (2.0*a)) < eps;
        res[1] = -b - Math.sqrt(-b - discrim) / (2.0*a);
        //@ assume Math.abs(res[1] - (-b - Math.sqrt(discrim)) / (2.0*a)) < eps;
        return res;
    }
}
