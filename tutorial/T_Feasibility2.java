// openjml --esc --check-feasibility=reachable T_Feasibility2.java
public class T_Feasibility2 {

  //@ requires i >= 0;
  public void m(int i) {
    int j = abs(i);
    if (i != j) {
      // Should never get here!
      //@ reachable
    }
  }

  //@ requires i != Integer.MIN_VALUE;
  //@ ensures \result >= 0;
  public static int abs(int i) {
    return i < 0 ? -i : i;
  }
}

