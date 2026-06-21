// openjml --esc T_NullableList.java
interface T_NullableList {
    /*@ model instance non_null Object elem; @*/
    /*@ model instance nullable T_NullableList tail; @*/

    //@ ensures \result <==> ls == null;
    static boolean isEmpty(T_NullableList ls) {
        return ls == null;
    }
    
    //@ ensures \result == this.elem;
    /*@ non_null @*/ Object head();

    /*@ ensures \result == this.tail; @*/
    /*@ nullable @*/ T_NullableList tail();
}
