// openjml --esc T_assert4.java

public class T_assert4 {
  public int f;

  public void example(/*@ nullable */ T_assert4 t) {
    //@ check t != null; // ERROR, because not necessarily so
    int k = t.f; // ERROR because t might be null
  }

  public void example2(/*@ nullable */ T_assert4 t) {
    //@ assert t != null; // ERROR, because not necessarily so
                          // but subsequently assumes it is true
    int k = t.f; // OK
  }

}
