// openjml --esc GenderedWithEquals.java
public interface GenderedWithEquals {
    //@ model instance String gender;

    //@ ensures \result == gender.equals("female");
    /*@ spec_pure @*/ boolean isFemale();

    /*@ also
      @    ensures (obj instanceof GenderedWithEquals)
      @             ==> (!gender.equals(((GenderedWithEquals)obj).gender)
      @                   ==> !\result);
      @*/
    public /*@ pure @*/ 
    boolean equals(/*@ nullable @*/ Object obj);
}
