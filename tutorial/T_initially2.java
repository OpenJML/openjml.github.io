// openjml --esc T_initially2.java
public class T_initially2 {

  public int width;
  public int length;

  //@ requires 0 < width < length;
  //@ ensures this.width == width && this.length == length;
  public T_initially2(int width, int length) {
    this.width = width;
    this.length = length;
  }

  //@ ensures this.width == 0 && this.length == 0;
  public T_initially2() {
    this(0,0);
  }

  //@ public initially 0 < width < length;

}
