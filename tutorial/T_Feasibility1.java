// openjml --esc --check-feasibility=exit T_Feasibility1.java
public class T_Feasibility1 {

  //@ requires i < 0;
  //@ ensures \result > 0;
  public int m(int i) {
    //@ assume i > 0;
    return i;
  }
}

