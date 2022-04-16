// openjml --esc --esc-bv=true T_BVMult.java
public class T_BVMult {

  //@ code_java_math
  public void test(long i) {
    long square = i*i;
    //@ assert -16000 < i < 16000 ==> square < Integer.MAX_VALUE; 
  }
}
   
