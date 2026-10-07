// openjml --esc T_frame3.java
public class T_frame3 {

  public int counter1;
  public int counter2;

  //@ requires counter1 < Integer.MAX_VALUE;
  //@ assignable counter1;
  //@ ensures counter1 == 1 + \old(counter1);
  public void increment1() {
    counter1 += 1;
  }

  //@ requires counter2 < Integer.MAX_VALUE;
  //@ assignable counter2;
  //@ ensures counter2 == 1 + \old(counter2);
  public void increment2() {
    counter2 += 1;
  }
  
  public void test() {
    counter1 = 0;
    counter2 = 0;
    increment1();
    //@ assert counter1 == 1;
    //@ assert counter2 == 0;
  }

  public void test2() {
    counter1 = 0;
    counter2 = 0;
    increment2();
    //@ assert counter1 == 0;
    //@ assert counter2 == 1;
  }
}
  
