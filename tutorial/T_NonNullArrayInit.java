// openjml --esc T_NonNullArrayInit.java
public class T_NonNullArrayInit {
    private /*@ spec_public nullable @*/ String[] array;
    private /*@ spec_public non_null @*/ String[] nna = array;

    public final String emptyString = "";

    public T_NonNullArrayInit(int sz) {
        //@ assume 0 < sz < Integer.MAX_VALUE;
        array = new String[sz];
        int i = 0;
        //@ assert array != null && array.length == sz;
        for (i = 0; i < sz; i++) {
            //@ assume 0 <= i;
            //@ assert i < array.length;
            //@ assume (\forall int j; 0 <= j < i; array[j] == emptyString);
            array[i] = emptyString;
            //@ assume (\forall int j; 0 <= j <= i; array[j] == emptyString);
        }
        //@ assume (\forall int j; 0 <= j < sz; array[j] == emptyString);
        nna = (/*@ non_null @*/ String[]) array;
        //@ assert (\forall int j; 0 <= j < sz; nna[j] == emptyString);
    }
}

