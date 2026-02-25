// openjml --esc --nullable-by-default T_MultipleBehaviors3.java
public class T_MultipleBehaviors3 {

    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@  ensures true;
    //@  signals (Exception e) false;
    //@ also
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only IllegalArgumentException;
    //@  ensures false;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new IllegalArgumentException();
        if (i < 0 || j < i || a.length < j) throw new IllegalArgumentException();
        return;
    }
}
