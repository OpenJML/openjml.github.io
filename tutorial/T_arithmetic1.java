// openjml --esc T_arithmetic1.java
public class T_arithmetic1 {
  public int increment(int i) {
    int new_i = i+1;   // ERROR: may overflow!
    //@ assert new_i == i+1;   // ERROR: may fail!
    return new_i;
  }
}
