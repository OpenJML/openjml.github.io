// openjml --esc ScreenPointAns.java
public class ScreenPointAns {
    public static final int MAX_SIZE = 2048;
    
    private /*@ spec_public @*/ int x, y;
    //@ public invariant 0 <= x < MAX_SIZE;
    //@ public invariant 0 <= y < MAX_SIZE;

    //@ requires 0 <= xv < MAX_SIZE;
    //@ requires 0 <= yv < MAX_SIZE;
    //@ ensures x == xv && y == yv;
    public ScreenPointAns(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ requires 0 <= x+mv < MAX_SIZE;
    //@ assignable x;
    //@ ensures x == \old(x+mv);
    public void moveRight(int mv) {
        x += mv;
    }

    //@ requires 0 <= y+mv < MAX_SIZE;
    //@ assignable y;
    //@ ensures y == \old(y+mv);
    public void moveUp(int mv) {
        y += mv;
    }

    public static void test() {
        //@ assert 0 <= 5;
        ScreenPointAns p = new ScreenPointAns(5, 7);
        java.util.Random r = new java.util.Random();
        int mv = r.nextInt(-4096, 4096);

        if (0 <= p.x + mv && p.x + mv < MAX_SIZE) {
            p.moveRight(mv);
            //@ assert 0 <= p.x < MAX_SIZE;
        }
        if (0 <= p.y + mv && p.y + mv < MAX_SIZE) {
            p.moveUp(mv);
            //@ assert 0 <= p.y < MAX_SIZE;
        }
    }
}
