public class MethodCallsEx1 {

    //@ requires 0 < x <= Integer.MAX_VALUE / 2;
    //@ requires 0 < y <= Integer.MAX_VALUE / 2;
    //@ ensures Math.abs(\result - ((x+y)/2.0)) < 1e-9;
    //@ pure
    public double averageMeasures(int x, int y) {
        if (isNonNegative(x) && isNonNegative(y)) {
            return (x+y)/2.0;
        }
        throw new IllegalArgumentException();
    }

    //@ ensures \result <==> 0 <= i;
    //@ pure
    public boolean isNonNegative(int i) {
        return 0 <= i;
    }

}
