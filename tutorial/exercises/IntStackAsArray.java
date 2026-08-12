// openjml --esc IntStackAsArray.java
public class IntStackAsArray implements IntStack {

    //@ public model \datagroup size; //@ in state;

    private int _size; //@ in size;
    private int[] elems; //@ in state;

    //@ private invariant 0 <= _size <= MAX_SIZE;
    //@ private invariant elems.length == MAX_SIZE;

    public IntStackAsArray() {
        _size = 0;
        elems = new int[MAX_SIZE];
    }

    //@ also
    //@   reads size;
    //@ also
    //@  private normal_behavior
    //@   ensures \result == _size;
    //@ spec_pure helper    
    public int size() {
        return _size;
    }

    public int nthElement(int n) {
        //@ assert elems.length == MAX_SIZE;
        //@ assert n < _size;
        //@ assert n < MAX_SIZE;
        return elems[n];
    }

    public int top() {
        return elems[_size-1];
    }

    //@ also
    //@  private normal_behavior
    //@   assignable elems[_size];
    public void push(int i) {
        elems[_size] = i;
        _size += 1;
    }

    //@ also
    //@  assignable size;
    public void pop() {
        //@ assert 0 < _size;
        _size -= 1;
        //@ assert (\forall int k; 0 <= k < _size; elems[k] == \pre(elems[k]));
    }
}
