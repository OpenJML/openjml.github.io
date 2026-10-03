// openjml --rac T_RacExit.java
public class T_RacExit {

  //@ diverges true;
  public static void main(String... args) {
    //@ assert args.length == 1;  // ERROR: assertion may be false!
    System.exit(10);
  }
}
