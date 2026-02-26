// openjml --esc T_PureMethod2.java
// Intentionally not in visible web-page, just checked
public class T_PureMethod2 {

  public static class Counter {
    //@ spec_public
    private int count;

    //@ spec_public
    final private int maxCount;

    //@ requires max >= 0;
    //@ ensures count == 0 && maxCount == max;
    //@ pure
    public Counter(int max) {
      count = 0;
      maxCount = max;
    }

    //@ requires count < maxCount;
    //@ assigns count;
    //@ ensures count == \old(count+1);
    public void count() { ++count; }

    //@ ensures \result == (count > 0);
    //@ spec_pure
    public boolean isAnythingCounted() {
       return count > 0;
    }

    //@ ensures \result == !(count < maxCount);
    //@ spec_pure
    public boolean atMax() {
       return count >= maxCount;
    }
  }

  public void test() {
    Counter c = new Counter(2);
    //@ assert !c.isAnythingCounted() && !c.atMax();
    c.count();
    //@ assert c.isAnythingCounted() && !c.atMax();
    c.count();
    //@ assert c.isAnythingCounted() && c.atMax();
  }
}
