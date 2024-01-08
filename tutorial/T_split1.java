// openjml --esc --split= --progress --no-show-summary $@
public class T_split1 {
  //@ requires 0 <= i <= 2; // to limit counterexaqmples to one value, for deterministic tests
  //@ ensures i == 2;
  public static int m(int i) {
    boolean p = i > 0;
    //@ split;
    if (p) {
      //@ split;
      switch (i) {
        case 1: break;
        case 2: break;
        default: break;
      }
    } else {
    }
    //@ show p,i;
    return i;
  }
}
