// openjml --esc --split= --progress --no-show-summary $@
public class T_split1 {
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
