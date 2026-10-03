// openjml --esc T_halt3.java
public class T_halt3 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ assert i < 10;   // ERROR: may be false!
    } else {
      //@ halt;
      //@ assert i < -10;   //
    }
    return i;   // ERROR: may violate postcondition!
  }
}
  
