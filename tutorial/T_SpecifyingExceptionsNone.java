// openjml --esc T_SpecifyingExceptionsNone.java
public class T_SpecifyingExceptionsNone {

    //@ signals_only \nothing;
    public int getHash(String str, int tableSize) {
        if(tableSize == 0) {
            throw new IllegalArgumentException();  // ERROR: can't throw this!
        }
	return str.length() % tableSize;
    }
}
