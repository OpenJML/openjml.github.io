// openjml --esc T_Exception4a.java
//@ nullable_by_default
public class T_Exception4a {

    public static class V {
        public int value;
    }

    //@ ensures \result == a[i];
    public int value(int[] a, int i) {
        return a[i];
    }
}
