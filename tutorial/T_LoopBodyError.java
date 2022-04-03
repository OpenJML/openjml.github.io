// ## openjml -esc --solver-seed=42 T_LoopBodyError.java
public class T_LoopBodyError {

  public void setToRamp(int[] a) {
    //@ maintaining 0 <= i < a.length;
    //@ maintaining \forall int k; 0 <= k < i; a[k] == k;
    //@ loop_writes i, a[*];
    //@ decreases a.length -i;
    for (int i = 0; i < a.length; i++) {
        a[i] = i;
        //@ show i, a.length;
    }
    //@ assert \forall int i; 0 <= i < a.length; a[i] == i;
  }
}
