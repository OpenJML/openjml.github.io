public class FrameCondEx1Ans {
    private /*@ spec_public @*/ int maxValue;
    private /*@ spec_public @*/ int x;
    private /*@ spec_public @*/ int y;

    //@ ensures x == xv && y == yv;
    //@ pure
    public FrameCondEx1Ans(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ assignable maxValue;
    //@ ensures x == maxValue || y == maxValue;
    //@ ensures x <= maxValue && y <= maxValue;
    public void determineMax() {
        if (xGreaterThanY()) {
            maxValue = x;
        } else {
            maxValue = y;
        }
    }

    //@ ensures \result <==> (x > y);
    // //@ pure
    public boolean xGreaterThanY() {
        return x > y;
    }

    public void test() {
        FrameCondEx1Ans fc12 = new FrameCondEx1Ans(1,2);
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
        fc12.determineMax();
        //@ assert fc12.maxValue == 2;
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
    }
}
