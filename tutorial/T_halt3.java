// openjml --esc $@
public class T_halt3 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ assert i < 10;
    } else {
      //@ halt;
      //@ assert i < -10;
    }
    return i;
  }
}
  
