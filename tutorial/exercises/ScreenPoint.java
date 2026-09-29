// openjml --esc ScreenPoint.java
public class ScreenPoint {
    public static final int MAX_SIZE = 2048;
    
    private /*@ spec_public @*/ int x, y;

    //@ requires 0 <= xv < MAX_SIZE;
    //@ requires 0 <= yv < MAX_SIZE;
    //@ ensures x == xv && y == yv;
    public ScreenPoint(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ requires Integer.MIN_VALUE <= x+mv <= Integer.MAX_VALUE;
    //@ assignable x;
    //@ ensures x == \old(x+mv);
    public void moveRight(int mv) {
        x += mv;
    }

    //@ requires Integer.MIN_VALUE <= y+mv <= Integer.MAX_VALUE;
    //@ assignable y;
    //@ ensures y == \old(y+mv);
    public void moveUp(int mv) {
        y += mv;
    }

    public static void test() {
        //@ assert 0 <= 5;
        ScreenPoint p = new ScreenPoint(5, 7);
        java.util.Random r = new java.util.Random();
        int mv = r.nextInt(-4096, 4096);

        p.moveRight(mv);
        //@ assert 0 <= p.x < MAX_SIZE;
        p.moveUp(mv);
        //@ assert 0 <= p.y < MAX_SIZE;
    }
}
