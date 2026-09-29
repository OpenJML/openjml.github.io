// openjml --esc Log.java
public class Log {
    private /*@ spec_public @*/ String text = "";

    //@ assignable text;
    //@ ensures text == \old(text + s);
    public void add(String s) {
        text += s;
    }

    public void test() {
        Log l = new Log();
        l.add("something");        
        int oldlen = text.length();
        l.add("something else");
        //@ assert oldlen <= text.length();
    }

}
