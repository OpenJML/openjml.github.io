// openjml --esc T_arithmetic3.java
public class T_arithmetic3 {
  public int abs(int i) {
      if (0 <= i) {
          return i;
      } else {
          //@ assert -i > 0;
          return -i;   // ERROR: see text!
      }
  }
}
