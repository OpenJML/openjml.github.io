// openjml --esc T_Nullness1.java
public class T_Nullness1 {
  //@ pure
  public static boolean has(String s, char c) {
    return s.indexOf(c) != -1;  // note: implicitly s is not null
  }

  static /*@ pure nullable */ String make(int i) {
    if (i<0) return null;
    return String.valueOf(new char[i]);
  }

  public static void test(/*@ nullable */ String ss) {
    boolean b = has(ss,'a');  // ERROR: may fail implicit precondition of has!
    b = has(make(2), 'a');   // ERROR: result of make may be null!
  }
}
