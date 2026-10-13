// openjml --esc T_arithmetic2.java
public class T_arithmetic2 {
  public int increment(int i) {
    //@ assume i < Integer.MAX_VALUE;
    int new_i = i+1;
    //@ assert new_i == i+1;
    return new_i;
  }
}
