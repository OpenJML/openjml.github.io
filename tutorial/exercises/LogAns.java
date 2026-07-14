// openjml --esc LogAns.java
public class LogAns {
    private /*@ spec_public @*/ String text = "";

    //@ public constraint \old(text.length()) <= text.length();

    //@ assignable text;
    //@ ensures text == \old(text + s);
    public void add(String s) {
        text += s;
    }

    public void test() {
        LogAns l = new LogAns();
        l.add("something");        
        int oldlen = text.length();
        l.add("something else");
        //@ assert oldlen <= text.length();
    }

}
