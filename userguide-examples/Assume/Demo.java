public class Demo {

  static public int demo(int i) {
    if (i > 0) return 1;
    //@ assume i < 0;
    return i;
  }
  @org.jmlspecs.annotation.SkipEsc
  @org.jmlspecs.annotation.SkipRac
  public static void main(String ... args) {
     int i = args.length == 0 ? 0 : Integer.parseInt(args[0]);
     demo(i);
  }
}
