// openjml --esc $@
public class T_show3 {
  //@ public invariant data.length >= 10;
  //@ spec_public
  private int[] data = new int[10];
  //@ requires i >= 0;
  public int data(int i) {
    int r = data[i];
    //@ show i, r;
    return r;
  }
}

