// openjml --esc MultipleViewPointImpl.java
public class MultipleViewPointImpl implements MultipleViewPoint {
    private final double _x; //@ in x; //@ in radius; //@ in angle;
    //@ private represents x = _x;
    private final double _y; //@ in y; //@ in radius; //@ in angle;
    //@ private represents y = _y; 

    /*@ axiom (\forall double a; !Double.isNaN(a);
      @                          a*a >= 0 && !Math.isNegativeZero(a*a)); @*/
    /*@ axiom (\forall double a; !Double.isNaN(a) && a > 0
      @                                   && a*a < Double.POSITIVE_INFINITY;
      @                          a*a > 0 && a*a != Double.POSITIVE_INFINITY);
      @*/
    /*@ axiom (\forall double a; !Double.isNaN(a)
      @                          && a*a < Double.POSITIVE_INFINITY;
      @                          a != Double.POSITIVE_INFINITY);
      @*/
    //@ axiom (\forall double a,b; !Double.isNaN(b); a*a + b*b >= 0);
    //@ axiom _x*_x + _y*_y >= 0;
    /*@ axiom (\forall double a; !Double.isNaN(a) && Math.isPositiveZero(a);
      @                          a >= 0); @*/
    //@ axiom (\forall double a; !Double.isNaN(a) && a >= 0; !Double.isNaN(Math.sqrt(a)));
    /*@ axiom (\forall double a,b; !Double.isNaN(a) && !Double.isNaN(b);
      @                            !Double.isNaN(Math.atan2(a,b))); @*/
    //@ private represents radius = Math.sqrt(_x*_x + _y*_y);
    //@ private represents angle = Math.atan2(_y,_x);

    //@ requires !Double.isNaN(xv) && xv*xv < Double.POSITIVE_INFINITY;
    //@ requires xv != Double.NEGATIVE_INFINITY;
    //@ requires !Double.isNaN(yv) && yv*yv < Double.POSITIVE_INFINITY;
    //@ requires yv != Double.NEGATIVE_INFINITY;
    //@ ensures !Double.isNaN(x) && !Double.isNaN(y);
    //@ ensures x == xv && y == yv;
    public MultipleViewPointImpl(double xv, double yv) {
        if (xv == -0.0) { _x = 0.0; } else {_x = xv; }
        //@ assume !Math.isNegativeZero(_x);
        if (yv == -0.0) { _y = 0.0; } else {_y = yv; }
        //@ assume !Math.isNegativeZero(_y);
        //@ assume !Double.isNaN(radius);
        //@ assume !Double.isNaN(angle);        
    }

    public double x() {
        return _x;
    }

    public double y() {
        return _y;
    }

    public double radius() {
        // The following assumption is needed because the current ESC cannot
        // reason about mathematical functions such as sqrt.
        //@ assume Math.abs(Math.sqrt(x*x + y*y) - Math.sqrt(_x*_x + _y*_y)) < EPS;
        return Math.sqrt(_x*_x + _y*_y);
    }

    public double angle() {
        // The following assumption is needed because the current ESC cannot
        // reason about mathematical functions such as atan2.
        //@ assume Math.abs(Math.atan2(y,x) - Math.atan2(_y,x)) < EPS;
        return Math.atan2(_y,_x);
    }
}
        
