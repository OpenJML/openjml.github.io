// openjml --esc LemmaExample.java
public class LemmaExample {

    //@ public normal_behavior
    //@   old long msecs = 1000 * Integer.toUnsignedLong(s);
    //@   ensures \result == msecs;
    //@ pure
  public static long fromUnsigned(int s) {
      //@// Takes much longer to prove without this lemma
      //@ use lemmaToUnsignedLong(s);
      long t = 1000 * ( 0xFFFF_FFFFL & s );
      return t;
  }

  //@ public normal_behavior
  //@   ensures (0xFFFF_FFFFL & i) == Integer.toUnsignedLong(i);
  //@ model public spec_pure static void lemmaToUnsignedLong(int i) {}
}
