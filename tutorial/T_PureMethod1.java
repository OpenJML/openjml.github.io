// openjml --esc --progress $@
public class T_PureMethod1 {

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
    //@ pure
    public boolean isAnythingCounted() {
       return count > 0;
    }

    //@ ensures \result == !(count < maxCount);
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
