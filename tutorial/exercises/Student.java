// openjml --esc Student.java
public class Student {
    private /*@ spec_public @*/ String firstName = "";
    private /*@ spec_public @*/ String lastName = "";
    private /*@ spec_public @*/ int grade;
    private /*@ spec_public @*/ double GPA;
    private /*@ spec_public @*/ long id;
    private /*@ spec_public @*/ static long count = 0;

    public Student(String firstName, String lastName, int grade, double GPA) { 
        //@ assume count < Long.MAX_VALUE;
        count++;   // ERROR: may fail!
		
        this.firstName = firstName;
        this.lastName = lastName;
        this.grade = grade;
        this.GPA = GPA;
        this.id = count;
    }
	
    public void createStudents() {
        Student s1 = new Student("John", "Doe", 12, 3.7);
        Student s2 = new Student("Jane", "Doe", 11, 2.5);
        //@ assert s1.id < s2.id;   // ERROR: may fail!
    }
}
