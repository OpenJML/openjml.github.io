// openjml --esc StudentAns.java
public class StudentAns {
    private /*@ spec_public @*/ String firstName = "";
    private /*@ spec_public @*/ String lastName = "";
    private /*@ spec_public @*/ int grade;
    private /*@ spec_public @*/ double GPA;
    private /*@ spec_public @*/ long id;
    private /*@ spec_public @*/ static long count = 0;

    //@ public normal_behavior
    //@    requires 0 < firstName.length();
    //@    requires 0 < lastName.length();
    //@    requires 1 <= grade <= 12;
    //@    requires 0 <= GPA <= 4.0 && !Double.isNaN(GPA);
    //@    requires count < Long.MAX_VALUE;
    //@    assignable count;
    //@    ensures this.firstName == firstName;
    //@    ensures this.lastName == lastName;
    //@    ensures this.grade == grade;
    //@    ensures this.GPA == GPA;
    //@    ensures this.id == count;
    //@    ensures count == \old(count) + 1;
    public StudentAns(String firstName, String lastName, int grade, double GPA) { 
        // assumption moved to precondition
        count++;
		
        this.firstName = firstName;
        this.lastName = lastName;
        this.grade = grade;
        this.GPA = GPA;
        this.id = count;
    }
	
    //@ requires count < Integer.MAX_VALUE-1;
    public void createStudents() {
        Student s1 = new Student("John", "Doe", 12, 3.7);
        Student s2 = new Student("Jane", "Doe", 11, 2.5);
        //@ assert s1.id < s2.id;
    }
}
