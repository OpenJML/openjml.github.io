// openjml --esc T_MultipleBehaviors3e.java
public class T_MultipleBehaviors3e {

    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@  ensures true;
    //@  signals (Exception e) false;
    //@ also
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only IllegalArgumentException;
    //@  ensures false;
    public void inrange(/*@ nullable @*/ int[] a,   // ERROR: parsing problem!
                        int i, int j) {
        if (a == null) throw new IllegalArgumentException();
        if (i < 0 || j < i || a.length < j) throw new IllegalArgumentException();
        return;
    }
}
