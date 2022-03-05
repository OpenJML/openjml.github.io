// openjml --esc $@
public class T_initially1 {

  public int width;
  public int length;

  //@ ensures this.width == width && this.length == length;
  public T_initially1(int width, int length) {
    this.width = width;
    this.length = length;
  }

  //@ ensures this.width == 0 && this.length == 0;
  public T_initially1() {
    this(0,0);
  }

  //@ public initially 0 < width < length;

}
