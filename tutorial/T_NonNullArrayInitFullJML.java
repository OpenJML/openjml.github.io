// openjml --esc T_NonNullArrayInitFullJML.java
public class T_NonNullArrayInitFullJML {
    private /*@ spec_public nullable @*/ String[] array;
    private /*@ spec_public non_null @*/ String[] nna = array;

    public final String emptyString = "";

    //@ requires 0 < sz < Integer.MAX_VALUE;
    //@ ensures array != null;
    //@ ensures (\forall int j; 0 <= j < sz; nna[j] == emptyString);
    public T_NonNullArrayInitFullJML(int sz) {
        array = new String[sz];
        //@ maintaining 0 <= i <= sz;
        //@ maintaining (\forall int j; 0 <= j < i; array[j] == emptyString);
        for (int i = 0; i < sz; i++) {
            array[i] = emptyString;
        }
        nna = (/*@ non_null @*/ String[]) array;
    }
}

