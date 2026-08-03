public class Animal implements Gendered {
    protected boolean _gen; //@ in gender;
    /*@ protected represents gender
      @        = (_gen ? "female" : "male"); 
      @*/

    //@ public model int age;
    protected int _age = 0; //@ in age;
    //@ protected represents age = _age;

    //@ requires g.equals("female")||g.equals("male");
    //@ ensures gender.equals(g) && age == 0;
    public Animal(String g) 
    { _gen = g.equals("female"); }

    /*@  requires 0 <= a && a <= 150;
      @  assignable age;
      @  ensures age == a; @*/
    public void fastSetAge(int a) 
    { _age = a; }

    //@ requires g.equals("female")||g.equals("male");
    //@ assignable gender;
    //@ ensures gender.equals(g);
    public void changeGender(String g) 
    { _gen = g.equals("female"); }

    public /*@ pure @*/ boolean isFemale() 
    { return _gen; }

    /*@   requires 0 <= a && age <= a <= 150;
      @   assignable age;
      @   ensures age == a;
      @*/
    public void setAge(int a) 
    { if (_age <= a && a <= 150) { _age = a; } }
}
