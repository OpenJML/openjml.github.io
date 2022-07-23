// openjml --esc T_halt2.java
public class T_halt2 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ halt;
      //@ assert i < 10;
    } else {
      //@ halt;
      //@ assert i < -10;
    }
    return i;
  }
}
  
