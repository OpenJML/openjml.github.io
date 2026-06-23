public class FrameCondEx1 {
    private /*@ spec_public @*/ int maxValue;
    private /*@ spec_public @*/ int x;
    private /*@ spec_public @*/ int y;

    //@ ensures x == xv && y == yv;
    //@ pure
    public FrameCondEx1(int xv, int yv) {
        x = xv;
        y = yv;
    }
    
    //@ ensures maxValue == x || maxValue == y;
    //@ ensures x <= maxValue;
    //@ ensures y <= maxValue;
    public void determineMax() {
        boolean xgty = xGreaterThanY();
        if (xgty) {
            maxValue = x;
        } else {
            maxValue = y;
        }
    }

    //@ ensures \result <==> (x > y);
    public boolean xGreaterThanY() {
        return x > y;
    }

    public void test() {
        FrameCondEx1 fc12 = new FrameCondEx1(1,2);
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
        fc12.determineMax();
        //@ assert fc12.maxValue == 2;
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
    }
}
