// openjml --esc OldAndOrderingEx2Key.java
public class OldAndOrderingEx2Key {
    private /*@ spec_public @*/ long number;
    private /*@ spec_public @*/ int aDivisor;

    //@ ensures number == n && aDivisor == div;
    //@ ensures n % div == 0;
    //@ requires div > 0;
    //@ requires n >= 0;
    public OldAndOrderingEx2Key(long n, int div) {
        number = n;
        aDivisor = div;
    }
}
    
        
