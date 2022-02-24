// openjml --esc $@
public class T_MultipleBehaviors4 {

    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@  ensures true;
    //@  signals (Exception e) false;
    //@ also
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only NullPointerException, ArrayIndexOutOfBoundsException;
    //@  ensures false;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new NullPointerException();
        if (i < 0 || j < i || a.length < j) throw new ArrayIndexOutOfBoundsException();
        return;
    }
}
