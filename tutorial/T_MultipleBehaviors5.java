// openjml --esc T_MultipleBehaviors5.java
public class T_MultipleBehaviors5 {

    //@ public normal_behavior
    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@ also public exceptional_behavior
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only NullPointerException, ArrayIndexOutOfBoundsException;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new NullPointerException();
        if (i < 0 || j < i || a.length < j) throw new ArrayIndexOutOfBoundsException();
        return;
    }
}
