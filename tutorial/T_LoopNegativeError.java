// openjml --esc T_LoopNegativeError.java
public class T_LoopNegativeError {

  public void setToRamp(int[] a) {
    //@ maintaining 0 <= i <= a.length;
    //@ maintaining \forall int k; 0 <= k < i; a[k] == k;
    //@ loop_writes i, a[*];
    //@ decreases -i;
    for (int i = 0; i < a.length; i++) {
        a[i] = i;
    }
    //@ assert \forall int i; 0 <= i < a.length; a[i] == i;
  }
}
