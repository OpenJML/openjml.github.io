// openjml --esc IntStack.java
public interface IntStack {
    static final int MAX_SIZE = 10000;

    //@ public model instance \datagroup elems;
    //@ public model instance \datagroup size;

    //@ public instance invariant 0 <= size() <= MAX_SIZE;

    //@ reads size;
    //@ ensures 0 <= \result <= MAX_SIZE;
    //@ spec_pure helper
    public int size();

    //@ requires 0 <= n < size();
    //@ reads elems;
    //@ spec_pure
    public int nthElement(int n);

    //@ reads size, elems;
    //@ requires 0 < size();
    //@ ensures \result == nthElement(size()-1);
    //@ spec_pure
    public int top();

    /*@ old int osize = size();
      @ requires osize < MAX_SIZE;
      @ assignable size, elems;
      @ ensures top() == i;
      @ ensures size() == osize+1;
      @ ensures (\forall int j; 0 <= j < osize;
      @                         nthElement(j) == \old(nthElement(j)));
      @*/
    public void push(int i);

    /*@ old int osize = size();
      @ requires 0 < osize;
      @ assignable size;
      @ ensures size() == osize-1;
      @ ensures (\forall int j; 0 <= j < osize-1;
      @                         nthElement(j) == \old(nthElement(j)));
      @*/
    public void pop();
}
