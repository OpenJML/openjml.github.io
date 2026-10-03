// openjml --esc T_halt1.java
public class T_halt1 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ assert i < 10;   // ERROR: may be false!
    } else {
      //@ assert i < -10;   // ERROR: may be false!
    }
    return i;   // ERROR: may violate postcondition!
  }
}
  
