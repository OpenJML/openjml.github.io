// openjml --esc T_NullableListImpl.java
public class T_NullableListImpl implements T_NullableList {
    /*@ non_null @*/ Object car; //@ in elem;
    //@ represents elem = car;
    /*@ nullable @*/ T_NullableList cdr; //@ in tail;
    //@ represents tail = cdr;

    public T_NullableListImpl(/*@ non_null @*/ Object e,
                              /*@ nullable @*/ T_NullableList ls) {
        this.car = e;
        this.cdr = ls;
    }

    public /*@ non_null @*/ Object head() {
        return this.car;
    }

    public /*@ nullable @*/ T_NullableList tail() {
        return this.cdr;
    }
}
                                           
