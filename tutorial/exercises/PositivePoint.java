// openjml --esc PositivePoint.java
public class PositivePoint extends Point {
    //@ public invariant 0 < x;
    //@ public invariant 0 < y;

    //@ requires 0 < xv && 0 < yv;
    //@ ensures x == xv && y == yv;
    public PositivePoint(int xv, int yv) {
        super(xv, yv);
    }
}
