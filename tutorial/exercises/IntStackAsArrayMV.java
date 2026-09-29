// openjml --esc IntStackAsArrayMV.java
public class IntStackAsArrayMV implements IntStackMV {

    private int _size; //@ in size;
    //@ private represents size = _size;
    private int _elems[]; //@ in elems; //@ maps _elems[*] \into elems;

    //@ private invariant _elems.length == MAX_SIZE;

    public IntStackAsArrayMV() {
        _size = 0;
        _elems = new int[MAX_SIZE];
    }

    public int size() {
        return _size;
    }

    public int nthElement(int n) {
        //@ assert _elems.length == MAX_SIZE;
        //@ assert n < _size;
        //@ assert n < MAX_SIZE;
        return _elems[n];
    }

    public int top() {
        return _elems[_size-1];
    }

    public void push(int i) {
        _elems[_size] = i;
        _size += 1;
    }

    public void pop() {
        //@ assert 0 < _size;
        _size -= 1;
        //@ assert (\forall int k; 0 <= k < _size; _elems[k] == \pre(_elems[k]));
    }
}
