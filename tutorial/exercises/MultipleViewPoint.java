// openjml --esc MultipleViewPoint.java
public interface MultipleViewPoint {
    public final double EPS = 0.1e-9;
    //@ public model instance double x;
    //@ public model instance double y;
    //@ public model instance double radius;
    //@ public model instance double angle;

    //@ public invariant !Double.isNaN(x) && !Double.isNaN(y);
    //@ public invariant !Math.isNegativeZero(x);
    //@ public invariant !Math.isNegativeZero(y);
    //@ public invariant x != Double.POSITIVE_INFINITY;
    //@ public invariant y != Double.NEGATIVE_INFINITY;
    //@ public invariant x*x < Double.POSITIVE_INFINITY;
    //@ public invariant y*y < Double.POSITIVE_INFINITY;

    //@ public invariant !Double.isNaN(radius) && !Double.isNaN(angle);
    //@ public invariant 0.0 <= radius;
    
    //@ ensures Math.abs(\result - x) < EPS;
    //@ spec_pure
    double x();

    //@ ensures Math.abs(\result - y) < EPS;
    //@ spec_pure
    double y();

    //@ ensures Math.abs(\result - radius) < EPS;
    //@ spec_pure
    double radius();

    //@ ensures Math.abs(\result - angle) < EPS;
    //@ spec_pure
    double angle();
}
