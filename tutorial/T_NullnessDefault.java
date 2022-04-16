// openjml --esc T_NullnessDefault.java
//@ non_null_by_default
public class T_NullnessDefault {

  public void test(String s) {
    int h = s.hashCode();
  }
}
