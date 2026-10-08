// openjml --esc OldAndOrderingEx2.java
public class OldAndOrderingEx2 {
    private /*@ spec_public @*/ long number;
    private /*@ spec_public @*/ int aDivisor;

    //@ ensures number == n && aDivisor == div;
    //@ ensures n % div == 0;   // ERROR: this is part of the problem!
    //@ requires n % div == 0;   // ERROR: this is part of the problem!
    //@ requires div > 0;
    //@ requires n >= 0;
    public OldAndOrderingEx2(long n, int div) {
        number = n;
        aDivisor = div;
    }
}
    
        
