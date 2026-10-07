// openjml --esc MethodCallsEx1Ans.java
public class MethodCallsEx1Ans {

    //@ requires 0 < x && 0 < y;
    //@ requires x+y <= Integer.MAX_VALUE;
    //@ ensures Math.abs(\result - ((x+y)/2.0)) < 1e-9;
    //@ pure
    public double averageMeasures(int x, int y) {
        if (isNonNegative(x) && isNonNegative(y)) {
            return (x+y)/2.0;
        }
        throw new IllegalArgumentException();
    }

    //@ ensures \result <==> 0 <= i;
    //@ spec_pure
    public boolean isNonNegative(int i) {
        return 0 <= i;
    }
}
