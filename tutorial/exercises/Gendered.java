// openjml --esc Gendered.java
public interface Gendered {
    //@ model instance String gender;

    //@ ensures \result == gender.equals("female");
    /*@ spec_pure @*/ boolean isFemale();
}
