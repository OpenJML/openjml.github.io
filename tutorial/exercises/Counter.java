// openjml --esc Counter.java
public class Counter {
    //@ public model int count;
    private int _count = 0; //@ in count;

    //@ represents count = _count;

    //@ requires count < Integer.MAX_VALUE;
    //@ assignable count;
    //@ ensures count == \old(count+1);
    public void inc() {
        _count++;
    }
}
