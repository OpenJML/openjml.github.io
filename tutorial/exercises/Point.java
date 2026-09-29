// openjml --esc Point.java
public class Point {
    protected /*@ spec_public @*/ int x, y;

    //@ ensures x == xv && y == yv;
    public Point(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ ensures \result == x;
    //@ spec_pure
    public int getX() {
        return x;
    }

    //@ ensures \result == y;
    //@ spec_pure
    public int getY() {
        return y;
    }

    //@ assignable x;
    //@ ensures x == newX;
    public void setX(int newX) {
        x = newX;
    }

    //@ assignable y;
    //@ ensures y == newY;
    public void setY(int newY) {
        y = newY;
    }
}
