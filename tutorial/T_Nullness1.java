// openjml --esc T_Nullness1.java
public class T_Nullness1 {

  public static boolean has(String s, char c) {
    return s.indexOf(c) != -1;
  }

  static /*@ nullable */ String make(int i) {
    if (i<0) return null;
    return String.valueOf(new char[i]);
  }

  public static void test(/*@ nullable */ String ss) {
    boolean b = has(ss,'a');
    b =  has(make(2), 'a');
  }
}
