class Parent {
  //@ requires i == 0;
  public void m(int i) {}
}

public class Demo extends Parent {

  //@ also
  //@   requires i < 0;
  //@ also
  //@   requires i >= 0;
  //@ behaviors disjoint;  // ERROR
  //@ behaviors local_disjoint; // OK
  @Override
  public void m(int i) {}

}

class Child extends Parent {

  //@ also
  //@   requires i <= 0;
  //@ also
  //@   requires i >= 0;
  //@ behaviors local_disjoint; // ERROR
  @Override
  public void m(int i) {}

}

