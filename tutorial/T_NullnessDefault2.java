// openjml --esc T_NullnessDefault2.java
//@ nullable_by_default
public class T_NullnessDefault2 {

  public void test(String s) {
    int h = s.hashCode();
  }
}
