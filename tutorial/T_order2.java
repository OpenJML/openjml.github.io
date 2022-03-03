// openjml --esc $@
//@ nullable_by_default // for the purpose of this example
public class T_order2 {

  //@ requires a != null;
  //@ requires a.length > 10;
  public void m(int[] a) {}

}
