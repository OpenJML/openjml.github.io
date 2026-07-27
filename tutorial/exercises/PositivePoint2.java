// openjml --esc PositivePoint2.java
public class PositivePoint2 extends Point {
    //@ public invariant 0 < x;
    //@ public invariant 0 < y;

    //@ requires 0 < xv && 0 < yv;
    //@ ensures x == xv && y == yv;
    public PositivePoint2(int xv, int yv) {
        super(xv, yv);
    }

    //@ also
    //@   requires 0 < newX;
    //@   assignable x;
    //@   ensures x == newX;
    public void setX(int newX) {
        //@ check 0 < newX; // invalid!
        x = newX;
    }

    //@ also
    //@   requires 0 < newY;
    //@   assignable y;
    //@   ensures y == newY;
    public void setY(int newY) {
        //@ check 0 < newY; // invalid!
        y = newY;
    }
}
