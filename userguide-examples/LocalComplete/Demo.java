class Parent {
  //@ requires i == 0;
  public void m(int i) {}
}

public class Demo extends Parent {

  //@ also
  //@   requires i < 0;
  //@ also
  //@   requires i > 0;
  //@ behaviors complete;  // OK
  //@ behaviors local_complete; // ERROR
  @Override
  public void m(int i) {}

}
