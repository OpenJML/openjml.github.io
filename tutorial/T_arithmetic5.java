// openjml --esc T_arithmetic5.java
public class T_arithmetic5 {
  //@ code_java_math
  public int inc_as_in_java(int i) { 
    int new_i = i+1;
    //@ assert new_i == \java_math(i+1);
    return new_i;
  }
}
