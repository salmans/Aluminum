package minalloy;
/* This class implements a program that performs basic comparisons between Alloy and Aluminum solutions.*/

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import kodkod.instance.Bounds;

import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.opts.BooleanOption;
import org.kohsuke.args4j.opts.FileOption;
import org.kohsuke.args4j.opts.IntOption;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import test.translator.A4Options;
import test.translator.A4Solution;
import test.translator.TranslateAlloyToKodkod;
import minalloy.translator.MinA4Options;
import minalloy.translator.MinA4Solution;
import minalloy.translator.MinTranslateAlloyToKodkod;
import minsolver.MinSolution;


public final class AluminumTester {
	/**
	 * This class stores minimal solutions and how they are related to each other wrt isomorphism.
	 */
	private static final class AluminumSolution{
		//The solution wrapped in this instance.
		final MinSolution solution;
		//The isomorphism group this solution is being assigned to. This index is the same as 
		//the minimal returned by Aluminum and isomorphic to this solution.
		final int groupIndex;
		
		public AluminumSolution(MinSolution solution, int groupIndex){
			this.solution = solution;
			this.groupIndex = groupIndex;
		}
	}
    /*
     * Execute every command in every file.
     *
     * This method parses every file, then execute every command.
     *
     * If there are syntax or type errors, it may throw
     * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
     * You should catch them and display them,
     * and they may contain filename/line/column information.
     */
    public static void main(String[] args) throws Err {
    	//The input spec file
    	FileOption optInput = new FileOption("-i");
    	//The output file
    	FileOption optOutput = new FileOption("-o");
    	//Symmetry Breaking (off by default)
    	IntOption optSymmetryBreaking = new IntOption("-sb", 20);
    	//Symmetry Breaking (off by default)
    	IntOption optSkolemDepth = new IntOption("-sk", 0);    	
    	//Symmetry Breaking (off by default)
    	BooleanOption optIsomorphicSolutions = new BooleanOption("-iso");
    	//Distribution of Alloy models wrt Aluminum models
    	FileOption optDistributionLog = new FileOption("-dl");
    	//Output verbosity
    	IntOption optVerbosity = new IntOption("-v", 0);
    	
    	CmdLineParser optParser = new CmdLineParser();
    	optParser.addOption(optInput);
    	optParser.addOption(optOutput);
    	optParser.addOption(optSymmetryBreaking);
    	optParser.addOption(optIsomorphicSolutions);
    	optParser.addOption(optSkolemDepth);
    	optParser.addOption(optDistributionLog);
    	optParser.addOption(optVerbosity);
    	
    	try{
    		optParser.parse(args);
    	}
    	catch(CmdLineException e){
    		System.err.println(e.getMessage());
    	}

    	if(optInput.value == null){
    		System.err.println("No input file is provided!");
    		System.exit(0);
    	}
    	if(optOutput.value == null){
    		System.err.println("No output file is provided!");
    		System.exit(0);
    	}
    	
    	System.out.println("Running AluminumTester for ");
    	System.out.println("-i = " + optInput.value.getPath());
    	System.out.println("-o = " + optOutput.value.getPath());
    	System.out.println("-v = " + optVerbosity.value);
    	System.out.println("-dl = " + optDistributionLog.value);
    	System.out.println("-sb = " + optSymmetryBreaking.value);
    	System.out.println("-iso = " + optIsomorphicSolutions.value);
    	
    	test(optInput, optOutput, optSymmetryBreaking, optSkolemDepth, optIsomorphicSolutions, optDistributionLog, optVerbosity);
    }
	
	/**
	 * Loads Kodkod's classes by loading a dummy spec.
	 */
	private static void test(FileOption optInput, FileOption optOutput, IntOption optSymmetryBreaking, IntOption optSkolemDepth, BooleanOption optIsomorphicSolutions,
			FileOption optDistributionLog, IntOption optVerbosity) throws Err{
		long startTime = System.currentTimeMillis();
		
		boolean logDistribution = optDistributionLog.value != null; 
		
		Set<String> uniqueSolutions = new LinkedHashSet<String>();
		
		
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };		
		
        Module world = CompUtil.parseEverything_fromFile(rep, null, optInput.value.getAbsolutePath());
        
        // Choose some default options for how you want to execute the commands
        MinA4Options aluminumOptions = new MinA4Options();
        A4Options alloyOptions = new A4Options();
        aluminumOptions.symmetry = optSymmetryBreaking.value;
        aluminumOptions.skolemDepth = optSkolemDepth.value;
        alloyOptions.symmetry = optSymmetryBreaking.value;
        alloyOptions.skolemDepth = optSkolemDepth.value;

		boolean foundError = false;
		int totalErrors = 0;
		int minimalSolutions = 0;
		int isomorphicMinimalSolutions = 0;
		
		// Lots of concatenation to a long string. Best to use a buffer.
		StringBuffer data = new StringBuffer();
		StringBuffer distributionLog = null;
		if(logDistribution)
			distributionLog = new StringBuffer("Distribution log for " + optInput.value.getPath() + "\n\n");
        
    	for(Command command: world.getAllCommands())
        {
    		if(logDistribution){
    			distributionLog.append("Executing command: " + command + " -----\n");
    			distributionLog.append("Alloy Solution\tMinimal Solution\tIsomorphism Group\n");
    		}
            System.out.print("Running Aluminum to build minimal solutions for command: " + command + ": ");

        	MinA4Solution aluminum = MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, aluminumOptions);
        	List<MinSolution> initialSolutions = new ArrayList<MinSolution>();
        	
        	while(aluminum.satisfiable()){
        		if(uniqueSolutions.add(aluminum.toString())){
        			initialSolutions.add(aluminum.getCurrentSolution());
        		}
        		aluminum = aluminum.next();
        		
        		System.out.print(".");
        	}

        	minimalSolutions = initialSolutions.size();
        	
        	// Print the number here and later on (in case it takes a long time to run)
        	System.out.println("\n  Got "+minimalSolutions+" minimal solutions from Aluminum.");

        	List<AluminumSolution> aluminumSolutions = new ArrayList<AluminumSolution>();
        	
        	if(optIsomorphicSolutions.value){
        		System.out.print("Building isomorphic solutions for the minimal solutions ....");
        		aluminumSolutions = getIsomorphicSolutions(initialSolutions, aluminum.getBounds());
            	System.out.println("Done!");
            	isomorphicMinimalSolutions = aluminumSolutions.size();

            	System.out.println("  Got "+isomorphicMinimalSolutions+" ismorphic+original minimal solutions.");
        	}else{
        		for(int i = 0; i < initialSolutions.size(); i++){ aluminumSolutions.add(new AluminumSolution(initialSolutions.get(i), i));}
        	}
        	
            System.out.print("Running Alloy for command: " + command + ": ");
        	int counter = 0;
        	A4Solution alloy = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, alloyOptions);
        	
        	System.out.println("Done!");
        	    
    		// Reduce output spam. Also, writing to the screen is expensive. 
        	int nEveryFewChecks = 100;
        	int nEveryFewDots = 10;
        	
        	while(alloy.satisfiable()){
        		boolean foundMinimal = false;
        		counter++;
        		
        		if(counter % nEveryFewChecks == 0)
        			System.out.print("Checking solution " + counter + ": ");
        		
        		int dotCounter = 1;
        		for(int i = 0; i < aluminumSolutions.size(); i++){
        			if(counter % nEveryFewChecks == 0 && dotCounter % nEveryFewDots == 0)
        				System.out.print(".");
        			dotCounter++;
        			
        			int comparison = SolutionComparator.compare(aluminumSolutions.get(i).solution, alloy.getCurrentSolution(), aluminum.getBounds(), alloy.getBounds());
        			
        			if(!foundMinimal)
        				foundMinimal = (comparison == -1 || comparison == 0);
        			
    				if(comparison == 1){
    					foundError = true;
    					totalErrors++;
            			data.append( "The following solution is not minimal: \n\n" + aluminumSolutions.get(i).toString() + "\n\n" +
            					"because of \n\n" + alloy.getCurrentSolution().toString() + "\n\n" +
            					"-------------------------------------\n");
    				}
    				
    				//Log distribution
    				if(logDistribution){
    					if(comparison == -1 || comparison ==0){
    						distributionLog.append(counter + "\t" + i + "\t" + aluminumSolutions.get(i).groupIndex + "\n");
    					}
    				}
        		}
        		
        		
        		if(!foundMinimal){
        			System.out.println("Error!");
        			data.append("Couldn't find a minimal solution for: \n\n" + alloy.getCurrentSolution().toString() + "\n" + 
        					"-------------------------------------\n");
        			foundError = true;
        			totalErrors++;    
        			
        			//Stops after visiting the first inconsistency:
        			break;
        		}
        		else{
        			if(optVerbosity.value > 0){
        				data.append("This is fine: \n\n" + alloy.getCurrentSolution().toString() + "\n" + 
        						"-------------------------------------\n");   
        			}
        			
    				if(counter % nEveryFewChecks == 0)
    					System.out.println("OK!");        			
        		}
        			
        		
        		alloy = alloy.next();
        	} // end for each Alloy model
        	
        	// Separator to help find break between command results 
        	System.out.println("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
        } // end for each command
        
    	//Writing the output
    	if(foundError){
    		System.out.println(totalErrors + " inconsistencies were found! Please read the output file for details.");
            try{
        		writeData(optOutput.value, data.toString());
            }
            catch(IOException e){
            	System.err.println(e.getMessage());
            	System.exit(0);
            }        		
    	}
    	else{
    		System.out.println("The experiment terminated successfully!");
            try{
        		writeData(optOutput.value, "The experiment terminated successfully!");
            }
            catch(IOException e){
            	System.err.println(e.getMessage());
            	System.exit(0);
            }        		        		
    	}
    	
    	//Writing the distribution log 
		if(logDistribution){
            try{
        		writeData(optDistributionLog.value, distributionLog.toString());
            }
            catch(IOException e){
            	System.err.println(e.getMessage());
            	System.exit(0);
            }        		
		}

    	
    	System.out.println("Total Execution Time: " + (System.currentTimeMillis() - startTime));
    	System.out.println("Inconsistencies: " + totalErrors);
    	System.out.println("Minimal Solutions: " + minimalSolutions);
    	if(optIsomorphicSolutions.value)
    		System.out.println("Isomorphic Minimal Solutions: " + isomorphicMinimalSolutions);    	
	}
	
	private static void writeData(File file, String data) throws IOException{
		FileWriter fstream = new FileWriter(file);
		BufferedWriter out = new BufferedWriter(fstream);
		
		out.write(data);
		
		out.close();
	}
	
	
	private static List<AluminumSolution> getIsomorphicSolutions(List<MinSolution> input, Bounds bounds){
		// Do not build permutations if there are no results. 
		// (Avoid long delay + possible out-of-memory if there are large bounds.)
		List<AluminumSolution> results = new ArrayList<AluminumSolution>();
		
		if(input.size() == 0) return results;

		//For reporting purposes, we want to keep the original minimal models produced by Aluminum in
		//their current place in the list:
		for(int i = 0; i < input.size(); i++){ results.add(new AluminumSolution(input.get(i), i));}
		
 		for(int i = 0; i < input.size(); i++){
 			Set<MinSolution> solutions = IsomorphicSolutionBuilder.getIsomorphicSolutions(input.get(i), bounds);
 			for(MinSolution sol: solutions){
 				//Now, we should avoid duplicate entries. (This is not the best way of doing this but it is fine for now)
 				if(SolutionComparator.compare(input.get(i), sol, bounds, bounds) != 0){
 					results.add(new AluminumSolution(sol, i));
 				}
 			}
		}
 		
		return results;
	}	
}

// -i "c:\Users\Tim\research\wpi-brown\projects\aluminum\examples\misc\addressbook\addressBook2a.als" -o testout.txt -iso
// -i "c:\Users\Tim\research\wpi-brown\projects\aluminum\examples\change-impact\continue-small1.als" -o testout.txt -iso