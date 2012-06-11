import java.io.*;
import java.util.ArrayList;
import java.util.Scanner;

public class ExampleLoader {
	private class Content{
		private int numOfVars;
		private int numOfClauses;
		private ArrayList<ArrayList<Integer>> data;		
	}
	/**
	 * The example file.
	 */
	private final String fileName;
	/**
	 * the content of the example file loaded in this object
	 */
	private final ArrayList<ArrayList<Integer>> content;
	/**
	 * the number of propositional variables in the example file
	 */
	private final int numOfVars;
	
	/**
	 * the number of clauses in the example file
	 */
	private final int numOfClauses;
	
	public ExampleLoader(String fileName){
		this.fileName = fileName;
		Content content = loadFile();
		this.content = content.data;
		this.numOfVars = content.numOfVars;
		this.numOfClauses = content.numOfClauses;		
	}
	
	/**
	 * Loads an example file.
	 * @return the example file as a list.
	 */
	private Content loadFile(){
    	Content result = new Content();
    	result.data = new ArrayList<ArrayList<Integer>>();

    	try {		    
		    Scanner scanner = new Scanner(new FileInputStream(fileName));
		    try{
			    while (scanner.hasNextLine()){
			    	String currentLine = scanner.nextLine().trim();
			    	if(currentLine.length() == 0){
			    		continue;
			    	}
			    	else if(currentLine.charAt(0) == '%'){
			    		break;
			    	}
			    	else if(currentLine.charAt(0) == 'c'){
			    		//skip the comment line
			    		continue;
			    	}
			    	else if(currentLine.charAt(0) == 'p'){
			    		Content temp = parseProperties(currentLine);
			    		result.numOfVars = temp.numOfVars;
			    		result.numOfClauses = temp.numOfClauses;			    		
			    	}
			    	else{
			    		//parse the CNF
				    	ArrayList<Integer> clause = parseLine(currentLine);
				    	result.data.add(clause);
			    	}
		    	}
		    }
		    finally{
		    	scanner.close();
		    }
		}
		catch(Exception e){
			System.err.println(e.getMessage());
		}
	    
	    return result;
	}

	private Content parseProperties(String propertiesLine){
		Content result = new Content();
		String str = propertiesLine.trim();
		int index = str.indexOf(' ');
		
		//getting rid of 'p' at the beginning of the line;
		str = str.substring(index + 1).trim();
		index = str.indexOf(' ');
		
		//getting rid of file format;
		str = str.substring(index + 1).trim();
		
		index = str.indexOf(' ');
		result.numOfVars = new Integer(str.substring(0, index)).intValue();
		str = str.substring(index + 1).trim();
		result.numOfClauses = new Integer(str).intValue();
		
		return result;
	}
	
	/**
	 * Parses a line corresponding to a CNF and returns a list of propositions
	 * in the CNF.
	 * @param line a line from the input file.
	 * @return a list of propositions.
	 */
	private static ArrayList<Integer> parseLine(String line){
		ArrayList<Integer> result = new ArrayList<Integer>();
		String str = line.trim();
		
		int index = str.indexOf(' ');
		while(index != -1){
			result.add(new Integer(str.substring(0, index)));
			str = str.substring(index + 1).trim();
			index = str.indexOf(' ');
		}
		
		/*if(!str.equals("0")){
			System.err.println("The CNF did not terminate with a 0.");
			System.exit(0);
		}*/
		
		return result;
	}
	
	/**
	 * getter for content of this object
	 * @return the content
	 */
	public ArrayList<ArrayList<Integer>> getContent(){
		return content;
	}
	
	public int getNumOfVars(){
		return numOfVars;
	}
	
	public int getNumOfClauses(){
		return numOfClauses;
	}
	
	public static void main(String[] args){
		new ExampleLoader("/Users/Salman/Dropbox/PhD projects/programs/MinSolver/Examples/ex1/uf75-01.cnf");
	}
}
