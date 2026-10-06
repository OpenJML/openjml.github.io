// openjml --esc T_NonNullArrayInit.java
public class T_NonNullArrayInit {
    private /*@ spec_public nullable @*/ String[] array;
    private /*@ spec_public non_null @*/ String[] nna = array;

    public final String emptyString = "";

    //@ requires 0 < sz < Integer.MAX_VALUE;
    //@ ensures array != null;
    //@ ensures (\forall int j; 0 <= j < sz; array[j] == emptyString);
    //@ ensures (\forall int j; 0 <= j < sz; nna[j] == emptyString);
    public T_NonNullArrayInit(int sz) {
        array = new String[sz];
        //@ assert array != null && array.length == sz;
        for (int i = 0; i < sz; i++) {
            //@ assume 0 <= i < array.length;
            array[i] = emptyString;
        }
        //@ assume (\forall int j; 0 <= j < sz; array[j] == emptyString);
        nna = (/*@ non_null @*/ String[]) array;
        //@ assume (\forall int j; 0 <= j < sz; nna[j] == emptyString);
    }
}

