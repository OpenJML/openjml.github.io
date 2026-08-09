// openjml --esc T_MultipleBehaviors2.java
public class T_MultipleBehaviors2 {
  //@  requires a <= c && a <= c;
  //@  ensures \result == c;
  //@ also
  //@  requires a <= b && c <= b;
  //@  ensures \result == b;
  //@ also
  //@  requires b <= a && c <= a;
  //@  ensures \result == a;
  //@ pure
  public int max(int a, int b, int c) {
    return a >= b ? ( c >=  a ? c : a) : (c >= b ? c : b);
  }
}
