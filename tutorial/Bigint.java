// openjml --esc Bigint.java
public class Bigint {

  //@ ghost \bigint x;
  //@ ghost \bigint y;

  public void test() {
    //@ assert Math.abs(x) >= 0;
    //@ assert x != 0 && y != 0 ==> Math.gcd(x,y) > 0;
  }
}
