// openjml --esc AnimalWithEquals.java
public class AnimalWithEquals implements GenderedWithEquals,
           NormalSetAge, ExceptionalSetAge {
    protected boolean _gen; //@ in gender;
    /*@ protected represents gender
      @           = (_gen ? "female" : "male"); 
      @*/

    protected int _age = 0; //@ in age;
    //@ protected represents age = _age;
    
    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g) && age == 0;
    public AnimalWithEquals(String g) 
    { _gen = g.equals("female"); }

    public /*@ spec_pure @*/ boolean isFemale() 
    { return _gen; }

    public void setAge(int a) {
        if (_age <= a && a <= 150) { _age = a; }
    }

    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object obj) {
        if (!(obj instanceof AnimalWithEquals)) {
            return false;
        }
        AnimalWithEquals awe = (AnimalWithEquals) obj;
        // Following is needed when OpenJML is not able to reason about strings
        //@ assume (_gen == awe._gen) <==> gender.equals(awe.gender);
        if (awe == null || !(this._gen  == awe._gen)
            || !(this._age == awe._age)) {
            return false;
        }
        return true;
    }
}
