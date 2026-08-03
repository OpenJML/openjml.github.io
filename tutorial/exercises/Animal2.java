public class Animal2 implements Gendered,
           NormalSetAge, ExceptionalSetAge {
    protected boolean _gen; //@ in gender;
    /*@ protected represents gender
      @           = (_gen ? "female" : "male"); 
      @*/

    protected int _age = 0; //@ in age;
    //@ protected represents age = _age;
    
    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g);
    public Animal2(String g) {
        _gen = g.equals("female");
    }

    public /*@ pure @*/ boolean isFemale() 
    { return _gen; }

    public void setAge(int a) {
        if (_age <= a && a <= 150) { _age = a; }
    }
}
