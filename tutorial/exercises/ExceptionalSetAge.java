// openjml --esc ExceptionalSetAge.java
public interface ExceptionalSetAge extends Age {
    /*@   requires a < age;
      @   assignable age;
      @   ensures \old(age) == age; @*/
    void setAge(int a); 
}
