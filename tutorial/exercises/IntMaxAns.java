// openjml --esc IntMaxAns.java
public class IntMaxAns {
    /*@   requires y <= x;
      @   ensures \result == x;
      @ also
      @   requires x <= y;
      @   ensures \result == y;
      @*/
    //@ pure
    public static int max(int x, int y) {
        if (y <= x) {
            return x;
        } else {
            return y;
        }
    }

    public static void testMax() {
        int m1 = max(5, 7);
        //@ assert m1 == 7;
        int m2 = max(9, 7);
        //@ assert m2 == 9;
        int m3 = max(11,11);
        //@ assert m3 == 11;
    }
}
