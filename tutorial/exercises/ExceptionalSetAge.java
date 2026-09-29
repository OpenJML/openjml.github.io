// openjml --esc ExceptionalSetAge.java
public interface ExceptionalSetAge extends Age {
    /*@ exceptional_behavior
      @   requires a < age;
      @   assignable \nothing;
      @   signals_only IllegalArgumentException;
      @*/
    void setAge(int a); 
}
