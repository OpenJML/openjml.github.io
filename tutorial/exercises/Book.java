public class Book {
	//@ spec_public
	private String title;
	//@ spec_public
	private int pages;
	//@ spec_public
	private String author;
	//@ spec_public
	private String publication; //mm-dd-yy
	//@ spec_public
	private static int TBABooks = 0; 

	//@ public normal_behavior
	//@ 	requires title != "";
	//@ 	requires 0 < pages < Integer.MAX_VALUE;
	//@ 	requires author != "";
	//@ 	requires publication != "";
	//@ 	ensures this.title == title;
	//@ 	ensures this.pages == pages;
	//@ 	ensures this.author == author;
	//@ 	ensures this.publication == publication;
	//@ pure
	public Book(String title, int pages, String author, String publication) {
		this.title = title;
		this.pages = pages;
		this.author = author;
		this.publication = publication;		
	}
	
	//@ public normal_behavior
	//@ 	requires publication == "TBA";
	//@ 	assigns TBABooks;
	//@ 	ensures this.title == title;
	//@ 	ensures this.pages == pages;
	//@ 	ensures this.author == author;
	//@ 	ensures this.publication == publication;
	//@ 	ensures TBABooks == \old(TBABooks) + 1;
	public Book(String publication) {
		//@ assume 0 < TBABooks+1 < Integer.MAX_VALUE;
		TBABooks++;
		this.title = "TBA";
		this.pages = 0;
		this.author = "TBA";
		this.publication = publication;
	}

	public void createBooks() {
		Book b1 = new Book("TBA"); 
		Book b2 = new Book("1984", 328, "George Orwell", "06-08-49");
		Book b3 = new Book("The Great Gatsby", 208, "F. Scott Fitzgerald", "04-10-25");
		Book b4 = new Book("TBA");				
	}
}