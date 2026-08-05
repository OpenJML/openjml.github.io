// openjml --esc NormalSetAge.java
public interface NormalSetAge extends Age {
    /*@  requires 0 <= a && age <= a <= 150;
      @  assignable age;
      @  ensures age == a;    @*/
    public void setAge(int a);
}
