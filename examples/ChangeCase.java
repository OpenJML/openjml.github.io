public class ChangeCase {

  //@   requires 'A' <= c <= 'Z';
  //@   ensures 'a' <= \result <= 'z';
  //@ also
  //@   requires 'a' <= c <= 'z';
  //@   ensures 'A' <= \result <= 'Z';
  //@ also
  //@   requires !('A' <= c <= 'Z') && !('a' <= c <= 'z');
  //@   ensures \result == c;
  public char changeCase(char c) {
    char result = ' ';    
    if (c > 'z') {
      result = c;
    } else if (c >= 'a') {
      result =  (char)(c - 'a' + 'A');
    } else if (c > 'Z') {
      result =  c;
    } else if (c >= 'A') {
      result =  (char)(c - 'A' + 'a');
    } else {
      result = c;
    }
    return result;
  }

}

