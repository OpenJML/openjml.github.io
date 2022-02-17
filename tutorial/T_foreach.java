// openjml -esc T_foreach.java
public class T_foreach {

  //@ ensures \result == (\forall int i; 0 <= i < a.length; a[i] > 0);
  public boolean allPositive(int[] a) {
    //@ maintaining 0 <= \count <= a.length;
    //@ maintaining \forall int k; 0 <= k < \count; a[k] > 0;
    //@ loop_writes \nothing;
    //@ decreases a.length - \count;
    for (int i: a) {
      if (i <= 0) return false;
    }
    return true;
  }
}
