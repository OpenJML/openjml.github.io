// openjml --esc Real.java
public class Real {

  //@ ghost \real x;
  //@ ghost \real y;

  public void test() {
    //@ assert Math.abs(x) >= 0;
    //@ assert Math.max(x,y) >= Math.min(x,y);
    //@ assert Math.sin(x) >= -1;
  }
}

