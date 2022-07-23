// openjml --esc T_show4.java
public class T_show4 {
  //@ public invariant data.length >= 10;
  //@ spec_public
  private int[] data = new int[10];
  //@ requires i >= 0;
  public int data(int i) {
    //@ show i, data.length;
    int r = data[i];
    return r;
  }
}

