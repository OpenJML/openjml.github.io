public class Student {
	//@ spec_public
	private String firstName;
	//@ spec_public
	private String lastName;
	//@ spec_public
	private int grade;
	//@ spec_public
	private double GPA;
	//@ spec_public
	private long id;
	//@ spec_public
	private static long count = 0;

	//@ public normal_behavior
	//@ 	requires firstName != "";
	//@		requires lastName != "";
	//@ 	requires 1 <= grade <= 12;
	//@ 	requires 0 <= GPA <= 4.0 && !Double.isNaN(GPA);
	//@ 	requires count < Integer.MAX_VALUE;
	//@ 	assigns count;
	//@ 	ensures this.firstName == firstName;
	//@		ensures this.lastName == lastName;
	//@ 	ensures this.grade == grade;
	//@ 	ensures this.GPA == GPA;
	//@ 	ensures this.id == count;
	//@ 	ensures count == \old(count) + 1;
	public Student(String firstName, String lastName, int grade, double GPA) { 
		//@ assume count+1 < Integer.MAX_VALUE;
		count ++;
		
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
