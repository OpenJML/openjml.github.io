// openjml --esc IntStackMV.java
public interface IntStackMV {
    static final int MAX_SIZE = 10000;

    //@ public model instance \seq<Integer> elems;

    //@ public model instance int size;

    //@ public instance invariant 0 <= size <= MAX_SIZE;

    //@ reads size;
    //@ spec_pure
    public int size();

    //@ requires 0 <= n < size;
    //@ reads size, elems[n];
    //@ ensures \result == elems[n];
    //@ spec_pure
    public int nthElement(int n);


    //@ requires 0 < size <= MAX_SIZE;
    //@ reads size, elems;
    //@ ensures \result == elems[size-1];
    //@ spec_pure
    public int top();

    /*@ old int osize = size;
      @ requires osize < MAX_SIZE;
      @ assignable size, elems;
      @ ensures top() == i;
      @ ensures size == osize+1;
      @ ensures (\forall int j; 0 <= j < osize; elems[j] == \old(elems[j]));
      @*/
    public void push(int i);

    /*@ old int osize = size;
      @ requires 0 < osize;
      @ assignable size;
      @ ensures size == osize-1;
      @ ensures (\forall int j; 0 <= j < osize-1; elems[j] == \old(elems[j]));
      @*/
    public void pop();
}
