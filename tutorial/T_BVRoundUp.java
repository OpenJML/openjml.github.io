// openjml --esc T_BVRoundUp.java
public class T_BVRoundUp {

  //@ requires n <= 0x7ffffff0;
  //@ ensures n <= \result;
  //@ ensures \result <= n+15;
  //@ ensures (\result%16) == 0;
  //@ pure
  //@ code_java_math
  public int m1(int n) {
    return n + ((-n) & 0x0f);
  }
}

