// openjml --esc $@
//@ nullable_by_default // for the purpose of this example
public class T_order1 {

  //@ requires a.length > 10;
  //@ requires a != null;
  public void m(int[] a) {}

}
