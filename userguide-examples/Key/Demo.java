public class Demo {

  public static void test() {
    //@ assert \key("OPENJML",ESC); // OK when run in OpenJML and --esc
    //@ assert \key(A); // OK if A is defined as a key, ERROR otherwise
  }
}
