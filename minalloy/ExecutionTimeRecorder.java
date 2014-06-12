package minalloy;
/* This class implements a program that records the execution time of alloy specs.*/

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.StringTokenizer;

import kodkod.ast.Relation;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;

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
import minkodkod.ExplorationException;
import minkodkod.MinSolution;
import minkodkod.MinSolution.MinimizationHistory;


public final class ExecutionTimeRecorder {
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
    public static void main(String[] args) throws Err, IOException {
    	//The input spec file
    	FileOption optInput = new FileOption("-i");
    	//The output file
    	FileOption optOutput = new FileOption("-o");
    	//Produce minimal solutions (by default non-minimal)
    //	BooleanOption optMinimal = new BooleanOption("-m", false);
    	//Number of models to produce
    	IntOption optNumberOfModels = new IntOption("-n", 10);
    	//Symmetry Breaking (Equal to Aluminum's SB by default)
    	IntOption optSymmetryBreaking = new IntOption("-sb", 20);
    	// respect
    	BooleanOption optSBRespect = new BooleanOption("-sbrespect", false);
    	
    	//Record augmentation time
    	FileOption optAugmentation = new FileOption("-a");
    	//Number of trials
    	IntOption optNumberOfTrials = new IntOption("-t", 1);
    	//Record minimization history as opposed to logging execution time
    	BooleanOption optLogMinimizationHistory = new BooleanOption("-hist", false);
    	//Record the execution time for getting consistent facts
    	BooleanOption optLogConsistentFacts = new BooleanOption("-cf", false);    	

    	
    	CmdLineParser optParser = new CmdLineParser();
    	optParser.addOption(optInput);
    	optParser.addOption(optOutput);
    //	optParser.addOption(optMinimal);
    	optParser.addOption(optNumberOfModels);
    	optParser.addOption(optSymmetryBreaking);
    	optParser.addOption(optAugmentation);
    	optParser.addOption(optNumberOfTrials);
    	optParser.addOption(optLogMinimizationHistory);
    	optParser.addOption(optLogConsistentFacts);
    	optParser.addOption(optSBRespect);
    	
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
    	if(optLogMinimizationHistory.value){	//If -hist is active, then run it only for one trial for only minimal solutions
 //   		optMinimal.value = true;
    		optNumberOfTrials.value = 1;
    	}
    	if(optLogConsistentFacts.value){	//If -cf is active, then run it for only minimal solutions
 //   		optMinimal.value = true;
    	}    	
/*    	if(!optMinimal.value && optAugmentation.value != null){
    		System.err.println("Augmentation is only applicable on minimal model finding.");
    		System.exit(0);
    	}*/
    	if(optLogConsistentFacts.value && optLogMinimizationHistory.value){
    		System.err.println("One one of -hist or -cf can be active.");
    		System.exit(0);
    	}
    	
    	//TODO this is the worst code ever! Consider revision:
    	//if(optMinimal.value)
    		solveMinimal(optInput, optOutput, optNumberOfModels, optSymmetryBreaking, optAugmentation, optNumberOfTrials, 
    				optLogMinimizationHistory, optLogConsistentFacts);
    	//else
//    		solveNonMinimal(optInput, optOutput, optMinimal, optNumberOfModels, optSymmetryBreaking, optNumberOfTrials);
    }

    /**
     * Runs the tests using Aluminum
     * @throws IOException 
     */
	private static void solveMinimal(FileOption optInput, FileOption optOutput, 
			IntOption optNumberOfModels, 
			IntOption optSymmetryBreaking, FileOption optAugmentation, 
			IntOption optNumberOfTrials, BooleanOption optLogMinimizationHistory,
			BooleanOption optLogConsistentFacts) throws Err, IOException {
		
    
	    AluminumTester.clearFile(optOutput.value);
		
		//Loads a dummy model in order to load Kodkod classes.
		try{
			initMinimal();
		}
		catch(Exception e){
			System.err.println("Initialization error!");
			System.exit(0);
		}
		
		ArrayList<String> output = new ArrayList<String>();    	
        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };
        
        // Parse+typecheck the model
        System.out.println("Parsing+Typechecking "+optInput.value.getName());
        output.add("Spec: " + optInput.value.getName());
        
        System.out.println("-sb = " + optSymmetryBreaking.value);
        output.add("-sb = " + optSymmetryBreaking.value);
        System.out.println("-n = " + optNumberOfModels.value);
        output.add("-n = " + optNumberOfModels.value);
        System.out.println("-hist = " + optLogMinimizationHistory.value);
        output.add("-hist = " + optLogMinimizationHistory.value);
        System.out.println("-cf = " + optLogConsistentFacts.value + "\n");
        output.add("-cf = " + optLogConsistentFacts.value + "\n");        
        System.out.println("-t = " + optNumberOfTrials.value + "\n"); 
        
        Module world = CompUtil.parseEverything_fromFile(rep, null, optInput.value.getPath());
        
        writeOutput(output, optOutput.value, true); 
        output.clear();
        
        // Choose some default options for how you want to execute the commands
        MinA4Options options = new MinA4Options();
        options.symmetry = optSymmetryBreaking.value;
        options.logMinimizationHistory = optLogMinimizationHistory.value;
        
        Stack<AugmentationElement> stack = null;
        if(optAugmentation.value != null){
        	try{
        		stack = parseAugmentationFile(optAugmentation.value);
        	}
        	catch(IOException e){
        		System.err.println(e.getMessage());
        		System.exit(0);
        	}
        }

        for (Command command: world.getAllCommands()) {
    		// Execute the command
    		System.out.println("Command: "+command + "-------------\n");
    		output.add("\n\nCommand:\t" + command.toString() + "-------------\n");
    		
    		/*if(command.check)
    		{
    			output.add("Skipped check.\n");
    			continue;
    		}*/
    		
    		// aggregate over all trials
    		Map<String, ArrayList<Integer>> unaryCounts = new HashMap<String, ArrayList<Integer>>(); 
    		
    		writeOutput(output, optOutput.value, true); 
            output.clear();
    		
            //Keeps the number of items in the output so far. We keep this number to add data in the next trials.
            int lineNumber = output.size();
    		
            ArrayList<Long> firstSolveTimes = new ArrayList<Long>();
            ArrayList<Long> translationTimes = new ArrayList<Long>();
            
        	for(int i = 0; i < optNumberOfTrials.value; i++){   
        		System.out.println("TRIAL " + (i + 1) + "------");

        		if(optLogMinimizationHistory.value){
        			System.out.println("invocations\telements\tattributes\trelations");
        			output.add("invocations\telements\tattributes\trelations");
        		}
        		else{
        			if(optLogConsistentFacts.value){
            			System.out.println("time\t#facts\ttotalaugmentation time");
            			//output.add("time\t#facts");
        			}else{
	        			System.out.println("time");
	        			//output.add("time");
        			}
        		}
        		
        		ArrayList<Long> times = new ArrayList<Long>();
        		
        		// Get first solutions actually writes the first column!
        		MinA4Solution ans = null;
        		try{
        			ans = getFirstSolution(rep, world, command, options, output, stack, 
        					  optLogMinimizationHistory.value, optLogConsistentFacts.value, i, lineNumber, times, unaryCounts);
        			translationTimes.add(times.get(0));
        			firstSolveTimes.add(times.get(1));
        		}
        		catch(ExplorationException e){
        			System.err.println(e.getMessage());
        			System.exit(0);
        		}
        		        		
        		long time = 0;
        		int consistentFacts = 0;
        		int counter = 1;
        		
        		if(!optLogConsistentFacts.value && !optLogMinimizationHistory.value);

        		while(ans.satisfiable())
        		{
            		long totalAugmentationTimeNS = 0;
      		
            		// Don't stop after num models in first trial; gotta compute median sizes.
            		// (But do refrain from printing or saving time infos)
        			if(counter == optNumberOfModels.value && i>0)
            		 	break;
        			
        			//System.out.println(ans.toString());
        			
        			//time = System.currentTimeMillis();        			
        			ans = ans.next();
        			//time = System.currentTimeMillis() - time;
        			time = ans.getCurrentSolution().stats().solvingTime();
        			
        			countUnary(unaryCounts, ans);
        			if(counter % 50 == 0)
        				System.out.println("   Counting model number "+counter);        	
        			
        			// save timing data if #models below ceiling in args
        			// (keep looping to count unaries)
        			if(counter < optNumberOfModels.value) {
        				String info = null;
        				if(optLogMinimizationHistory.value){        				
        					MinimizationHistory history = ans.getCurrentSolution().minimizationHistory;
        					
        					if(history == null) //The last unsatisfiable solution comes back with a null history.
        						break;
        				
        					info = history.SATSolverInvocations + "\t" + history.reducedElements + "\t" + history.reducedAttributes + "\t" + history.reducedRelations;
        				}else{
        					if(optLogConsistentFacts.value){
        						info = time + "\t" + consistentFacts + "\t" + (totalAugmentationTimeNS/1000000);        		
        					}
        					else{
        						info = new Long(time).toString();
        					}        				
        				}
        			
        				System.out.println(++counter + ": " + info);
        				if(i == 0)
        					output.add(info);
        				else{
        					if(!optLogConsistentFacts.value && !optLogMinimizationHistory.value)
        						output.set(counter + lineNumber, output.get(counter + lineNumber) + "\t" + info);
        					else
        						output.set(counter + lineNumber -1, output.get(counter + lineNumber - 1) + "\t" + info);        				
        				}
        			} // end if under # models
        			else
        				counter++;
        			
        		} // end for each solution
        		        		
        		//Writing the current state of data to a file.
    	        try{
    	        	//We are not keeping appending data to a previous log file.
    	        	writeOutput(output, optOutput.value, true);    	        	
    	        }
    	        catch(IOException e){
    	        	System.err.println(e.getMessage());
    	        }
    	        
        	}	  // end for each trial
        	
        	output.clear();
	        output.add("----------------------------------------------------");    	        
	        output.add("Medians of unary relation tuple counters: ");
	        for(String rname : unaryCounts.keySet()) {
	        	output.add(rname+": "+median(unaryCounts.get(rname))+" over "+unaryCounts.get(rname).size()+" scenarios.");
	        }        	
        	output.add("----------------------------------------------------");
    		output.add("\nAverage translation: "+avg(translationTimes));
    		output.add("Average first soln or unsat: "+avg(firstSolveTimes));    		
    		output.add("StdDev translation: "+stddev(translationTimes));
    		output.add("StdDev first soln or unsat: "+stddev(firstSolveTimes));
    		output.add("----------------------------------------------------");
    		
    		    		
    		try {
				writeOutput(output, optOutput.value, true);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
    		output.clear();

        } // end for each command
	}
		
	private static double avg(ArrayList<Long> vals) {
		double sum = 0;
		for(long val : vals) {
			sum = sum + val;
		}
		return sum / vals.size();
	}
	
	private static int median(ArrayList<Integer> vals) {
		Integer[] arr = vals.toArray(new Integer[vals.size()]);
		Arrays.sort(arr);
		//System.out.println(vals);
		//System.out.println(Arrays.toString(arr));
		int mididx = arr.length/2;
		
		if(arr.length % 2 == 0) {
			int m1 = arr[mididx-1]; 
			int m2 = arr[mididx];
			return (m1+m2)/2;
		}
		else {
			return arr[mididx];
		}		
	}
	
	private static double stddev(ArrayList<Long> vals) {						
		double mean = avg(vals);
		
		double temp = 0;
		for (long val : vals) {
			temp = temp + Math.pow(val - mean, 2);
		}
		
		// POPULATION stddev. sample would take -1 on the bottom
		// If double-checking in Excel, that's STDEVP, not STDEV
		return Math.sqrt(temp/vals.size());
	}
	
	private static MinA4Solution getFirstSolution(A4Reporter rep, Module world, Command command, 
			MinA4Options options, ArrayList<String> output, Stack<AugmentationElement> stack, boolean logMinimizationHistory, 
			boolean logConsistentFacts, int trial, int lineNumber, ArrayList<Long> times, Map<String, ArrayList<Integer>> unaryCounts)
					throws Err, ExplorationException{
        long time = 0;
        long translTime = 0;
        int consistentFacts = 0;
        
        //time = System.currentTimeMillis();
        MinA4Solution ans = MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
        //time = System.currentTimeMillis() - time;
        translTime = ans.getCurrentSolution().stats().translationTime();
        time = ans.getCurrentSolution().stats().solvingTime();
        
        countUnary(unaryCounts, ans);
        
        int counter = 1;

        while(stack!= null && !stack.empty()){
        	AugmentationElement aug = stack.pop();
        	while(counter != aug.solutionNumber){
        		ans = ans.next();
        		counter ++;
        	}
        	
        	//time = System.currentTimeMillis();
        	ans = ans.augment(aug.augmentingFact, null);
        	translTime = ans.getCurrentSolution().stats().translationTime();
        	time = ans.getCurrentSolution().stats().solvingTime();
        	//time = System.currentTimeMillis() - time;	
        }
        
		/*long totalAugmentationTimeNS = 0;		
        if(logConsistentFacts){ //When logging consistent facts, ignore the time to fetch the last model.
			if(ans.satisfiable()){
				//Get all the consistent facts:
    			time = System.currentTimeMillis();
    			Instance facts = ans.getConsistentFacts();
    			time = System.currentTimeMillis() - time;
    			
                consistentFacts = 0;	
                // Compute the total number of consistent facts:
                for(Relation relation: facts.relations()){
                	consistentFacts += facts.tuples(relation).size();
                }
                
                // Compute the time to augment the solution using the consistent facts:
                if(consistentFacts > 0) {	
                	//  if there are any consistent facts
                	for(Relation relation: facts.relations()){
                		for(Tuple tuple: facts.tuples(relation)){
                			// "This method provides nanosecond precision, but not necessarily nanosecond accuracy."
                        	long augmentationTimeNS = System.nanoTime();
                        	try{
                        		// No translation (so we can use the tuple string in raw form)
                        		ans = ans.augment(relation.toString()+tuple.toString(), null);
                        		augmentationTimeNS = System.nanoTime() - augmentationTimeNS;
	                        	totalAugmentationTimeNS += augmentationTimeNS;	                        	
                        		ans = ans.backtrack();
                        	}
                        	catch(ExplorationException e){
                        		System.err.println(e.getMessage());
                        		System.exit(1);
                        	} catch (IOException e) {
                        		System.err.println(e.getMessage());
                        		System.exit(2);
							}
                        	
                		}
                	}
                }
			}
			else{
				time = -1;
				consistentFacts = -1;
			}
        }
        */
        // see minsolver.computeDifference
        // elements = actual atoms that no longer get used
        // attributes: unary relations
        // relations: >1ary relations
        String info = null;
        if(logMinimizationHistory){
        	MinimizationHistory history = ans.getCurrentSolution().minimizationHistory;
        	if(history != null)
        		info = history.SATSolverInvocations + "\t" + history.reducedElements + "\t" + history.reducedAttributes + "\t" + history.reducedRelations;
        	else
        		info = "No solutions.";
        }
        else
        	info = new Long(time).toString();
        	/*
        else{
        	if(logConsistentFacts){
        		info = time + "\t" + consistentFacts + "\t" + (totalAugmentationTimeNS/1000000);        		
        	}
        	else{
        		info = new Long(time).toString();        		
        	}
        }*/                   
        
        times.add(translTime);
        times.add(time);
        
        if(!logMinimizationHistory && !logConsistentFacts)
        	System.out.println("translate: " + translTime);
        	
        System.out.println("1: " + info);
        if(trial == 0){
            if(!logMinimizationHistory && !logConsistentFacts)
            	output.add(new Long(translTime).toString());
        	output.add(info);
        }
        else{
            if(!logMinimizationHistory && !logConsistentFacts){
            	output.set(lineNumber, output.get(lineNumber)  + "\t" +translTime);
            	lineNumber++;
            }
        	output.set(lineNumber, output.get(lineNumber) + "\t"+ info);
        }
		
		return ans;
	}
		
	private static void countUnary(Map<String, ArrayList<Integer>> result, MinA4Solution ans) {		
		
		// Count how many atoms are in each unary relation and return counts as a map
		MinSolution kSol = ans.getCurrentSolution();
		if(!ans.satisfiable()) return;
		
		for(Relation r : kSol.instance().relations())
		{
			if(r.arity() == 1)
			{
				if(!result.containsKey(r.name()))
					result.put(r.name(), new ArrayList<Integer>());
								
				// mutation, not functional sets
				result.get(r.name()).add(kSol.instance().relationTuples().get(r).size());				
			}
		}				
	}

	/**
	 * Loads Kodkod's classes by loading a dummy spec.
	 */
	private static void initMinimal() throws Err{
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };		
		
        Module world = CompUtil.parseEverything_fromFile(rep, null, "resources/test.als");
        
        // Choose some default options for how you want to execute the commands
        MinA4Options options = new MinA4Options();
        options.symmetry = 20;
        
        for(Command command: world.getAllCommands())
        	MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);   
	}
	
	/**
	 * Runs the tests using Alloy 
	 */
	/*
	private static void solveNonMinimal(FileOption optInput, FileOption optOutput, 
			BooleanOption optMinimal, IntOption optNumberOfModels, 
			IntOption optSymmetryBreaking, IntOption optNumberOfTrials) throws Err {
		//Loads a dummy model in order to load Kodkod classes.
		try{
			initNonMinimal();
		}
		catch(Exception e){
			System.err.println("Initialization error!");
			System.exit(0);
		}		
		
		ArrayList<String> output = new ArrayList<String>();    	
        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };

        // Parse+typecheck the model
        System.out.println("Parsing+Typechecking "+optInput.value.getName());
        output.add("Spec: " + optInput.value.getName());
        
        System.out.println("-m = " + optMinimal.value);
        output.add("-m = " + optMinimal.value);
        System.out.println("-sb = " + optSymmetryBreaking.value);
        output.add("-sb = " + optSymmetryBreaking.value);
        System.out.println("-n = " + optNumberOfModels.value + "\n");
        output.add("-n = " + optNumberOfModels.value + "\n");
        
        Module world = CompUtil.parseEverything_fromFile(rep, null, optInput.value.getPath());

        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();
        options.symmetry = optSymmetryBreaking.value;

        for (Command command: world.getAllCommands()) {	
        	// Execute the command
        	System.out.println("Command: "+command + "-------------\n");
        	output.add("Command:\t" + command.toString() + "-------------\n");

    		if(command.check)
    		{
    			output.add("Skipped check.\n");
    			continue;
    		}
        	
            //Keeps the number of items in the output so far. We keep this number to add data in the next trials.
            int lineNumber = output.size();

        	for(int i = 0; i < optNumberOfTrials.value; i++){
        		System.out.println("TRIAL " + (i + 1) + "------");
        		System.out.println("time");
        		
        		long time = 0;
        		long translTime = 0;
        		//time = System.currentTimeMillis();
        		A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
        		//time = System.currentTimeMillis() - time;
        		translTime = ans.getCurrentSolution().stats().translationTime();
        		time = ans.getCurrentSolution().stats().solvingTime();
        		
        		int counter = 0;

        		System.out.println("0: " + translTime);
        		System.out.println("1: " + time);
        		if(i == 0){
        			output.add(new Long(translTime).toString());
        			output.add(new Long(time).toString());
        			counter++;
        		}
        		else{
        			output.set(lineNumber + counter, output.get(lineNumber + counter++) + "\t" + translTime);
        			output.set(lineNumber + counter, output.get(lineNumber + counter) + "\t" + time);
        		}

        		while(ans.satisfiable()){
        			if(counter == optNumberOfModels.value)
        				break;
        		
        			//time = System.currentTimeMillis();                	
        			ans = ans.next();
        			//time = System.currentTimeMillis() - time;
        			time = ans.getCurrentSolution().stats().solvingTime();

        			System.out.println(++counter + ": " + time);
        			if(i == 0)
        				output.add(new Long(time).toString());
        			else
        				output.set(counter + lineNumber, output.get(counter + lineNumber) + "\t" + time);
        		}
        		
        		//Write the results of this trial to the output.
                try{
                	//We do not support appending the data to the end of a previous report file.
                	//We simply write the current state of data after each trial.
                	writeOutput(output, optOutput.value, false);
                }
                catch(IOException e){
                	System.err.println(e.getMessage());
                }
        	}
        }        
	}*/
    
	/**
	 * Loads Kodkod's classes by loading a dummy spec.
	 */
	/*
	private static void initNonMinimal() throws Err{
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };		
		
        Module world = CompUtil.parseEverything_fromFile(rep, null, "resources/test.als");
        
        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();
        options.symmetry = 20;
        
        for(Command command: world.getAllCommands())
        	TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);   
	}
	*/
	
	/**
	 * Helper methods
	 */
    private static void writeOutput(ArrayList<String> output, File outputFile, boolean append) throws IOException{
    	FileWriter fstream = new FileWriter(outputFile,append);
    	BufferedWriter out = new BufferedWriter(fstream);
    	for(String str: output){
    		out.write(str + "\n");
    	}
    	out.close();
    }
    
    private static Stack<AugmentationElement> parseAugmentationFile(File file) 
    		throws IOException{
    	Stack<AugmentationElement> result = new Stack<AugmentationElement>();
    	
		FileReader fstream = new FileReader(file);
    	BufferedReader in = new BufferedReader(fstream);
    	
    	String currentLine;
    	while((currentLine = in.readLine()) != null){
    		//Skip comment lines
    		if(currentLine.startsWith("--"))
    			continue;
    		
    		StringTokenizer tokenizer = new StringTokenizer(currentLine, "\t");
    		AugmentationElement element = new AugmentationElement(
    				new Integer(tokenizer.nextToken()).intValue(), tokenizer.nextToken());
    		
    		result.add(element);
    	}
    	
    	in.close();
    	return result;
    }
}

/**
 * A data structure that holds information about a solution that is being augmented and
 * a fact that is augmenting the solution.
 */
class AugmentationElement {
	int solutionNumber;
	String augmentingFact;
	
	AugmentationElement(int solutionNumber, String augmentationFact){
		this.solutionNumber = solutionNumber;
		this.augmentingFact = augmentationFact;
	}
}


//-i test/akhawe/authn.als -o test/akhawe/authn.txt  -t 1 -n 10 -cf -m
// -i c:/users/tim/desktop/alloycnm.als -o c:/users/tim/desktop/out.txt -hist