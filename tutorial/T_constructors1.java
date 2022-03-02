// openjml --esc $@
public class T_constructors1 {

  public int width;
  public int height;

  //@ public normal_behavior
  //@   requires width >= 0 && height >= 0;
  //@   ensures this.width == width;
  //@   ensures this.height == height;
  //@ pure
  public T_constructors1(int width, int height) {
    this.width = width;
    this.height = height;
  }

  //@ public normal_behavior
  //@   ensures this.width == 0 && this.height == 0;
  //@ pure
  public T_constructors1() {
    this(0,0);
  }
}
