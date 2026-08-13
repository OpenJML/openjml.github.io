// openjml --esc IntStackAsArray.java
public class IntStackAsArray implements IntStack {

    private int _size; //@ in size;
    private int _elems[]; //@ in elems;

    //@ private invariant 0 <= _size <= MAX_SIZE;
    //@ private invariant _elems.length == MAX_SIZE;

    public IntStackAsArray() {
        _size = 0;
        _elems = new int[MAX_SIZE];
    }

    //@ also
    //@   reads size;
    //@ also
    //@  private normal_behavior
    //@   ensures \result == _size;
    //@ spec_pure helper    
    public int size() {
        //@ assume 0 <= _size <= MAX_SIZE;
        return _size;
    }

    //@ also
    //@  private normal_behavior
    //@   requires 0 <= n < _size;
    //@   reads _elems;
    //@   ensures \result == _elems[n];
    public int nthElement(int n) {
        //@ assert _elems.length == MAX_SIZE;
        //@ assert n < _size;
        //@ assert n < MAX_SIZE;
        return _elems[n];
    }

    public int top() {
        return _elems[_size-1];
    }

    // //@ also
    // //@  private normal_behavior
    // //@   assignable _size, _elems[_size];
    public void push(int i) {
        _elems[_size] = i;
        _size += 1;
    }

    //@ also
    //@  requires 0 < size();
    //@  assignable size;
    public void pop() {
        //@ assert 0 < _size;
        _size -= 1;
        //@ assert (\forall int k; 0 <= k < _size; _elems[k] == \pre(_elems[k]));
    }
}
