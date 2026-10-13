// openjml --esc T_arithmetic4.java
public class T_arithmetic4 {
  public int abs(int i) {
      //@ assume i != Integer.MIN_VALUE;
      if (0 <= i) {
          return i;
      } else {
          //@ assert -i > 0;
          return -i;
      }
  }
}
