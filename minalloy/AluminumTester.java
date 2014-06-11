package minalloy;
/* This class implements a program that performs basic comparisons between Alloy and Aluminum solutions.*/

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
import minkodkod.MinSolution;


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
		
		public String toString()
		{
			return solution.toString()+"\ngroupIndex:"+groupIndex;
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
    	// Force SB respect
    	BooleanOption optSBRespect = new BooleanOption("-sbrespect");
    	// Stop after n models
    	IntOption optCutoff = new IntOption("-c", 0);
    	
    	CmdLineParser optParser = new CmdLineParser();
    	optParser.addOption(optInput);
    	optParser.addOption(optOutput);
    	optParser.addOption(optSymmetryBreaking);
    	optParser.addOption(optIsomorphicSolutions);
    	optParser.addOption(optSkolemDepth);
    	optParser.addOption(optDistributionLog);
    	optParser.addOption(optVerbosity);
    	optParser.addOption(optSBRespect);
    	optParser.addOption(optCutoff);
    	
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
    	System.out.println("-sbrespect = " + optSBRespect.value);
    	
    	test(optInput, optOutput, optSymmetryBreaking, optSkolemDepth, optIsomorphicSolutions, 
    			optDistributionLog, optVerbosity, optSBRespect, optCutoff);
    }
	
	/**
	 * Loads Kodkod's classes by loading a dummy spec.
	 */
	private static void test(FileOption optInput, FileOption optOutput, IntOption optSymmetryBreaking, IntOption optSkolemDepth, BooleanOption optIsomorphicSolutions,
			FileOption optDistributionLog, IntOption optVerbosity, BooleanOption optSBRespect, IntOption optCutoff) throws Err{
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
        aluminumOptions.forceRespectSB = optSBRespect.value;        
        aluminumOptions.skolemDepth = optSkolemDepth.value;
        alloyOptions.symmetry = optSymmetryBreaking.value;
        alloyOptions.skolemDepth = optSkolemDepth.value;
        // SAT4J is the default                
        
		boolean foundError = false;
		int totalErrors = 0;
		int minimalSolutions = 0;
		int isomorphicMinimalSolutions = 0;
			
		try {
			clearFile(optOutput.value);
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		// Lots of concatenation to a long string. Best to use a buffer.
		StringBuffer data = new StringBuffer();
		StringBuffer distributionLog = null;
		if(logDistribution)
			distributionLog = new StringBuffer("Distribution log for " + optInput.value.getPath() + "\n\n");
        
    	for(Command command: world.getAllCommands())
        {
    		if(logDistribution){
    			distributionLog.append("Executing command: " + command + " -----\n");
    			distributionLog.append("Alloy Solution\tMinimal Solution\tIsomorphism Group\tComparison\n");
    		}
            System.out.print("Running Aluminum to build minimal solutions for command: " + command + ": \n");

            // Clear out the cache:
            uniqueSolutions.clear();
            
            // This call will do an initial solution-hunt. 
        	MinA4Solution aluminum = MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, aluminumOptions);
        	List<MinSolution> initialSolutions = new ArrayList<MinSolution>();        	        	
        	        	        	
        	int dupes = 0;
        	
        	while(aluminum.satisfiable() && (optCutoff.value == 0 || optCutoff.value > initialSolutions.size())){
        		// aluminum.toString() --- Alloy's renamed version of the instance
        		//   dupes will be spotted here: dupes if would be DISPLAYED the same
        		// but actually record the original, pre-alloy instance
        		if(uniqueSolutions.add(aluminum.toString())){        		
        			initialSolutions.add(aluminum.getCurrentSolution());
        		}
        		else {
        			dupes ++;        		
        		}        		
        		        		
        		//System.out.print(".");
        		//System.out.println(aluminum.getCurrentSolution());
        		//System.out.println(aluminum.toString());
        		if((initialSolutions.size() + dupes) % 100 == 0)        			
        			System.out.print("Fresh instance number: "+initialSolutions.size()+"; dupe count="+dupes+
        					"; hash="+aluminum.toString().hashCode()+
        					"; SBsat?="+aluminum.getCurrentSolution().isCanonical+"\n");
        		
        		// Is there another solution?
        		aluminum = aluminum.next();        			
        	}

        	System.out.print("\nTotal min instances: "+initialSolutions.size()+"; dupe count="+dupes);
        	minimalSolutions = initialSolutions.size();
        	
        	// Per command
        	int ordinalSumAlloy = 0;
        	int minInstanceCoverage = 0;
        	int ordinalSumAluminum = 0;
        	Set<Integer> wantToSeeClassesForOrdinal = new HashSet<Integer>();
        	
        	// Print the number here and later on (in case it takes a long time to run)
        	System.out.println("\n  Got "+minimalSolutions+" minimal solutions from Aluminum.");
        	System.out.println("\nTime since started translation: "+(System.currentTimeMillis()-startTime)+"ms.");
        	
        	
        	
        	////////////////////////////////////////////
        	////////////////////////////////////////////
        	// WARNING:
        	// Removing "remainder" relations in Aluminum
        	// means that the ontologies of instances returned
        	// by the two tools will not match. More work needs to
        	// be done if we are going to re-use this containment checking code.
        	////////////////////////////////////////////
        	////////////////////////////////////////////        	
        	
        	
        	
        	
        	
        	
        	
        	
        	List<AluminumSolution> aluminumSolutionsWithIsos = new ArrayList<AluminumSolution>();

        	// groupindex -> dupe groupindices
        /*	Map<Integer, Set<Integer>> dupeSolnMap = new HashMap<Integer, Set<Integer>>();
        	Set<Integer> isDupeOrdered = new HashSet<Integer>();
        	if(optIsomorphicSolutions.value){
        		System.out.println("Building isomorphic solutions for the minimal solutions ....");
        		// Will log # repeats in this call
        		aluminumSolutionsWithIsos = getIsomorphicSolutions(initialSolutions, aluminum.getSkolemBounds(), dupeSolnMap);
            	System.out.println("Done!");
            	
            	// Obtain count of duplicates from the map.
            	// It is NOT half of the number of entries (unless all classes are size=2):            	
            	for(Integer ii : dupeSolnMap.keySet())
            	{
            		for(Integer jj : dupeSolnMap.get(ii))
            		{
            			if(jj > ii)
            				isDupeOrdered.add(jj);
            		}
            		
            		// Populate in preparation for ordinal-sum production
            		if(!isDupeOrdered.contains(ii))
            			ordinalSumAluminum += (ii+1);
            		// Include ALL classes 
            		wantToSeeClassesForOrdinal.add(ii); // not i+1 (classes start with index 0)
            		
            	}
            	System.out.println("  Number of iso dupes:\n  "+isDupeOrdered.size());
            	System.out.println("  Duplication map: "+dupeSolnMap);
         		
         		
            	isomorphicMinimalSolutions = aluminumSolutionsWithIsos.size();

            	System.out.println("  Got "+isomorphicMinimalSolutions+" ismorphic+original minimal solutions.");
            	            	
        	}else{
        		for(int i = 0; i < initialSolutions.size(); i++)
        		{
        			aluminumSolutionsWithIsos.add(new AluminumSolution(initialSolutions.get(i), i));
        			
        			// Populate in preparation for ordinal-sum production
        			ordinalSumAluminum += (i+1);
        			wantToSeeClassesForOrdinal.add(i); // not i+1 (classes start with index 0)
        		}
        	        	
        	}        	        	        	        	
        	
        	*/
        	
            System.out.print("Running Alloy for command: " + command + ": ");        	
            
        	A4Solution alloy = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, alloyOptions);
        	
        	System.out.println("Done!");
        	    
    		// Reduce output spam. Also, writing to the screen is expensive. 
        	final int nEveryFewChecks = 100;
        	final int nEveryFewDots = 10;
        	        	
        	// Taken from SimpleReporter. We want to count only solutions that Alloy actually
        	// *SHOWS THE USER*. Alloy trims out duplicates using this hashset after solution
        	// generation (up to 100 times per model displayed):
        	// The set of Strings already enumerated for this current solution. 
            final Set<String> latestKodkods=new LinkedHashSet<String>();
        	
        	int counter = 0;        	
        	int tries = 0;
        	while(alloy.satisfiable() && (optCutoff.value == 0 || optCutoff.value > counter))
        	{        		
        		        		        		
        		// Do not count this solution if Alloy wouldn't display it (VITAL CHECK for fairness):
        		// (alloy.toString() is different from alloy.getCurrentSolution.toString())
        		if(!latestKodkods.add(alloy.toString()))
        		{        		
        			if (tries<100) 
        			{ 
        				tries++;
        				alloy = alloy.next();            			
        				continue;
        			}
        			// Otherwise, give up (as Alloy's visualizer would)        			        			
        		}
        		
        		
        		boolean foundMinimal = false;
        		counter++;
        	        		
        		// DEBUG
        	//	System.out.println("Alloy solution "+counter+" had this many atoms actually used: "+alloy.getAllAtoms());
        		
        		if(counter % nEveryFewChecks == 0)
        			System.out.println("Checking solution " + counter + "...");
        		
        		int dotCounter = 1;
        		for(int iAlumWithIsoIndex = 0; iAlumWithIsoIndex < aluminumSolutionsWithIsos.size(); iAlumWithIsoIndex++)
        		{
        			AluminumSolution thisAlumIsomorph = aluminumSolutionsWithIsos.get(iAlumWithIsoIndex);
        			
        			if(counter % nEveryFewChecks == 0 && dotCounter % nEveryFewDots == 0)
        				System.out.print(".");
        			dotCounter++;
        			
        			int comparison = SolutionComparator.compare(thisAlumIsomorph.solution, alloy.getCurrentSolution());
        			
        			if(!foundMinimal)
        				foundMinimal = (comparison == -1 || comparison == 0);
        			
    				if(comparison == 1){
    					foundError = true;
    					totalErrors++;
            			data.append( "The following Aluminum solution is not minimal:\n\n" + 
    					thisAlumIsomorph.toString() + "\n\n" +
            					"because Alloy gave something smaller:\n\n" + 
    					alloy.getCurrentSolution().toString() + "\n\n" +
            					"-------------------------------------\n");
    				}
    				
    				// Logging cone distribution
    			/*	if(logDistribution && dupeSolnMap.containsKey(thisAlumIsomorph.groupIndex))
    				{						
    					
    					//////////
    					// Calculate the ordinal sum for Alloy's iterator. If this is an exact
    					// match, and we need to count this iso class still:
    					if(comparison == 0)
    					{    						
    						if(wantToSeeClassesForOrdinal.remove(thisAlumIsomorph.groupIndex))
    						{
    							ordinalSumAlloy += counter; // Not +1; alloy starts with from 1 not 0
    							minInstanceCoverage = counter;
    							    	    							    							
    							wantToSeeClassesForOrdinal.removeAll(dupeSolnMap.get(thisAlumIsomorph.groupIndex));    							
    							
    							System.out.println("  MATCH for Ordinal Sum: "+thisAlumIsomorph.groupIndex+
    									" at Alloy Model "+counter+
    									"\n    Eliminating entire class:"+dupeSolnMap.get(thisAlumIsomorph.groupIndex)+" plus "+thisAlumIsomorph.groupIndex+
    									"\n    so total is: "+ordinalSumAlloy);
    						}
    					}
    					    					    					
    					//////////
    					// Log a row saying that this Alloy model is in the cone of this Aluminum isomorph
    					// (the isomorph isn't necessarily generated by Aluminum, but is a symmetry for easy comparison)
    					if(comparison == -1 || comparison == 0)
    					{
    						distributionLog.append(counter + "\t" + iAlumWithIsoIndex + "\t" + aluminumSolutionsWithIsos.get(iAlumWithIsoIndex).groupIndex + "\t" + comparison + "\n");
    					}
    				}*/
        		}
        		
        		/*
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
        			
        		*/
    				
        		alloy = alloy.next();
        	} // end for each Alloy model
        	
        	System.out.println("OS Alloy: "+ordinalSumAlloy);
        	System.out.println("OS Aluminum: "+ordinalSumAluminum);
      /*  	if(logDistribution)
        	{
        		distributionLog.append("OS Alloy:\t"+ordinalSumAlloy+"\n");
        		distributionLog.append("OS Aluminum:\t"+ordinalSumAluminum+"\n");
        		distributionLog.append("Min. Instance Coverage: \t"+minInstanceCoverage+"\n");
        	}
        	if(optIsomorphicSolutions.value && logDistribution)
        	{
        		distributionLog.append("Number of dupes:\t"+isDupeOrdered.size()+"\n");
        	}*/
        	System.out.println("Number of Alloy solutions processed (not counting same-string dupes): "+counter);
        	
        	// Separator to help find break between command results 
        	System.out.println("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
        	
        	
         	try {
        		writeData(optOutput.value, "File: " + optInput.value + ": ");
				writeData(optOutput.value, "Command: " + command + ": ");
				writeData(optOutput.value, "Alloy scenarios: " + counter );
				writeData(optOutput.value, "Aluminum scenarios: " + minimalSolutions);
				writeData(optOutput.value, "SB = " + optSymmetryBreaking.value);
				writeData(optOutput.value, "Force Respect SB = " + optSBRespect.value);
				writeData(optOutput.value, "Cutoff = " + optCutoff.value);
				writeData(optOutput.value, "\n");
				
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
        	        
        	
        } // end for each command
        
    	//Writing the output
    /*	if(foundError){
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
		}*/

    	
    	System.out.println("Total Execution Time: " + (System.currentTimeMillis() - startTime));
    	System.out.println("Inconsistencies: " + totalErrors);
    	System.out.println("Minimal Solutions: " + minimalSolutions);
    	/*if(optIsomorphicSolutions.value) {
    		System.out.println("Detected isomorphs of the minimal solutions for comparison: " + isomorphicMinimalSolutions);
    	}*/
	}
	
	
	
	private static void writeData(File file, String data) throws IOException{
		FileWriter fstream = new FileWriter(file, true);
		BufferedWriter out = new BufferedWriter(fstream);		
		out.write(data+"\n");		
		out.close();
	}
	
	static void clearFile(File file) throws IOException{
		FileWriter fstream = new FileWriter(file);
		BufferedWriter out = new BufferedWriter(fstream);					
		out.close();
	}
	
	
	
	private static List<AluminumSolution> getIsomorphicSolutions(List<MinSolution> inputInstances, Bounds skolemBounds, 
			Map<Integer, Set<Integer>> dupeSolnMap){
		// Do not build permutations if there are no results. 
		// (Avoid long delay + possible out-of-memory if there are large bounds.)
		List<AluminumSolution> results = new ArrayList<AluminumSolution>();
		
		if(inputInstances.size() == 0) return results;		
							
		//For reporting purposes, we want to keep the original minimal models produced by Aluminum in
		//their current place in the list:
		for(int i = 0; i < inputInstances.size(); i++) {
			// sanitizeToBounds removes every relation not in the Skolem bounds.
			// This effectively removes "labeling" relations inserted by Alloy.
			inputInstances.get(i).sanitizeToBounds(skolemBounds);
			results.add(new AluminumSolution(inputInstances.get(i), i));
			dupeSolnMap.put(i, new HashSet<Integer>());
		}
				
		
 		for(int instanceIndex = 0; instanceIndex < inputInstances.size(); instanceIndex++)
 		{ 			
 			// Build the solutions isomorphic to this one (UP TO KODKOD'S GREEDY DETECTION)
 			MinSolution thisInputInstance = inputInstances.get(instanceIndex);
 			Set<MinSolution> isosForThisInstance = IsomorphicSolutionBuilder.getIsomorphicSolutions(thisInputInstance, skolemBounds);
 			
 			// Log the number of repeats UP TO KODKOD's SYMMETRY DETECTION. The naive way is:
 			// For every input after this one, see if it's equal to something in the isos above.
 			// (Suffices to check only those *after* since isomorphism is symmetric)
 			for(int otherIndex = instanceIndex+1;otherIndex<inputInstances.size();otherIndex++ )
 			{
 				MinSolution otherInputInstance = inputInstances.get(otherIndex);
 				// Is otherInputInstance ~=_{kodkod} thisInputInstance?
 				for(MinSolution sol: isosForThisInstance)
 				{
 					if(SolutionComparator.compare(sol, otherInputInstance) == 0)
 					{ 						 					
 						// Don't break. Want to detect everything this dupe is iso for.
 						// (Note that that means the number of duplicates is NOT half the number of entries)
 						dupeSolnMap.get(instanceIndex).add(otherIndex);
 						dupeSolnMap.get(otherIndex).add(instanceIndex);
 					}
 				}
 			}
 			
 			// Add non-duplicates to the list: 			
 			for(MinSolution sol: isosForThisInstance){ 				 				
 				//Now, we should avoid duplicate entries. (This is not the best way of doing this but it is fine for now)
 				if(SolutionComparator.compare(thisInputInstance, sol) != 0){
 					results.add(new AluminumSolution(sol, instanceIndex));
 				}
 			} 			 			
		} 		 		 		 		
 		
		return results;
	}	
}

// -i "c:\Users\Tim\research\wpi-brown\projects\aluminum\examples\misc\addressbook\addressBook2a.als" -o testout.txt -iso
// -i "c:\Users\Tim\research\wpi-brown\projects\aluminum\examples\change-impact\continue-small1.als" -o testout.txt -iso

// Without -iso here, there is an immediate mismatch. Don't panic: it's just because no iso.
// -i "C:\Users\Tim\research\dj-git\test-git-sizes.als" -o "C:\Users\Tim\research\dj-git\testout.txt" -dl "C:\Users\Tim\research\dj-git\dl.txt"

// -i "C:\vbox\nat2\props.als" -o "C:\vbox\nat2\testout.txt" -dl "C:\vbox\nat2\dl.txt" -sb 1000
// -i "C:\vbox\nat2\javatypes.als" -o "C:\vbox\nat2\testout.txt" -dl "C:\vbox\nat2\dl.txt"