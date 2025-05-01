import org.jmlspecs.runtime.*;
public class Demo {

  //@ requires i >= 0;
  public static void outer(int i) {
    inner(i);
  }

  //@ requires i > 0;
  public static void inner(int i) {
  }

  public static void main(String ... args) {
    outer(1); // OK
    try {
      outer(-1); // Outer precondition fails
    } catch (JmlAssertionError.PreconditionEntry e) {
      System.out.println("OK");
    }
    try {
      outer(0); // Inner precondition fails
    } catch (JmlAssertionError.PreconditionEntry e) {
      throw e; // FAILURE;
    } catch (JmlAssertionError.Precondition e) {
      System.out.println("OK");
    }
    try {
      inner(0); // Precondition fails
    } catch (JmlAssertionError.PreconditionEntry e) {
      System.out.println("OK");
    }
  }
}
    

