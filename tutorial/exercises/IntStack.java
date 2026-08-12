// openjml --esc IntStack.java
public interface IntStack {
    static final int MAX_SIZE = 10000;

    //@ public model instance \datagroup state;

    //@ public instance invariant size() <= MAX_SIZE;

    //@ reads state;
    //@ spec_pure helper
    public int size();

    //@ requires 0 <= n < size();
    //@ reads state;
    //@ spec_pure
    public int nthElement(int n);

    //@ reads state;
    //@ requires 0 < size();
    //@ ensures \result == \old(nthElement(size()-1));
    //@ spec_pure
    public int top();

    //@ old int osize = size();
    //@ requires osize < MAX_SIZE;
    //@ assignable state;
    //@ ensures top() == i;
    //@ ensures size() == osize+1;
    //@ ensures (\forall int j; 0 <= j <= osize; nthElement(j) == \old(nthElement(j)));
    public void push(int i);

    //@ old int osize = size();
    //@ requires 0 < osize;
    //@ assignable state;
    //@ ensures size() == osize-1;
    //@ ensures (\forall int j; 0 <= j < osize-1; nthElement(j) == \old(nthElement(j)));
    public void pop();
}
