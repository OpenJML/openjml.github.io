public class Demo {

  private /*@ spec_public */ int count;

  //@ public constraint count > \old(count);

  //@ requires count < Integer.MAX_VALUE;
  //@ assignable count;
  public void increment() {
    count++;
  }

  //@ assignable \nothing;
  //@ ensures \result == count;
  public int count() {
    return count;
  }
}
