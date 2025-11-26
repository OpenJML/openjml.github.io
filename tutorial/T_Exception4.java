// openjml --esc T_Exception4.java
//@ nullable_by_default
public class T_Exception4 {

    public static class V {
        public int value;
    }

    //@ ensures \result == a[i];
    //@ signals (NullPointerException e) a == null;
    //@ signals (IndexOutOfBoundsException e) a != null && (i < 0 || i >= a.length);
    //@ signals_only Exception;
    public int value(int[] a, int i) {
        return a[i];
    }
}
