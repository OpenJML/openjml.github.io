public class Demo {
  public int f;

  //@ assigns \nothing;
  public void demo(int i) {
    f = i; // ERROR - f is not in assigns clause
  }
}
    
