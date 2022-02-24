// openjml --esc $@
public class T_MultipleBehaviors2 {
  //@  requires c >= a && c >= a;
  //@  ensures \result == c;
  //@ also
  //@  requires b >= a && b >= c;
  //@  ensures \result == b;
  //@ also
  //@  requires a >= b && a >= c;
  //@  ensures \result == a;
  //@ pure
  public int max(int a, int b, int c) {
    return a >= b ? ( c >=  a ? c : a) : (c >= b ? c : b);
  }
}
