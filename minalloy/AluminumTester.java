package minalloy;
/* This class implements a program that records the execution time of alloy specs.*/

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedHashSet;
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
    	BooleanOption optIsomorphicSolutions = new BooleanOption("-iso");
    	
    	
    	CmdLineParser optParser = new CmdLineParser();
    	optParser.addOption(optInput);
    	optParser.addOption(optOutput);
    	optParser.addOption(optSymmetryBreaking);
    	optParser.addOption(optIsomorphicSolutions);
    	
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
    	System.out.println("-sb = " + optSymmetryBreaking.value);
    	System.out.println("-iso = " + optIsomorphicSolutions.value);
    	
    	test(optInput, optOutput, optSymmetryBreaking, optIsomorphicSolutions);
    }
	
	/**
	 * Loads Kodkod's classes by loading a dummy spec.
	 */
	private static void test(FileOption optInput, FileOption optOutput, IntOption optSymmetryBreaking, BooleanOption optIsomorphicSolutions) throws Err{
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
        alloyOptions.symmetry = optSymmetryBreaking.value;

		boolean foundError = false;
		int totalErrors = 0;
		
    	String data = "";
        for(Command command: world.getAllCommands()){
            System.out.print("Running Aluminum to build minimal solutions for command: " + command + ": ");

        	MinA4Solution aluminum = MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, aluminumOptions);
        	Set<MinSolution> aluminumSolutions = new HashSet<MinSolution>();
        	
        	while(aluminum.satisfiable()){
        		if(uniqueSolutions.add(aluminum.toString())){
        			aluminumSolutions.add(aluminum.getCurrentSolution());
        			//data += aluminum.getCurrentSolution() + "\n\n";
        		}
        		aluminum = aluminum.next();
        		
        		System.out.print(".");
        	}
        	//data += "\n\n\n\n\n";
        	System.out.println("Done!");

        	
        	if(optIsomorphicSolutions.value){
        		System.out.print("Building isomorphic solutions for the minimal solutions ....");
        		aluminumSolutions = getIsomorphicSolutions(aluminumSolutions, aluminum.getBounds());
            	System.out.println("Done!");
        	}
        	
        	
            System.out.print("Running Alloy for command: " + command + ": ");
        	int counter = 0;
        	A4Solution alloy = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, alloyOptions);
        	
        	System.out.println("Done!");
        	        	
        	while(alloy.satisfiable()){
        		boolean foundMinimal = false;
                System.out.print("Checking solution " + (++counter) + ": ");
        		
        		for(MinSolution minimalSolution: aluminumSolutions){
        			System.out.print(".");
        			int comparison = minimalSolution.compareTo(alloy.getCurrentSolution());
        			
        			if(!foundMinimal)
        				foundMinimal = (comparison == -1 || comparison == 0);
        			
    				if(comparison == 1){
    					foundError = true;
    					totalErrors++;
            			data += "The following solution is not minimal: \n\n" + minimalSolution.toString() + "\n\n" +
            					"because of \n\n" + alloy.getCurrentSolution().toString() + "\n\n" +
            					"-------------------------------------\n";
    				}
        		}
        		
        		
        		if(!foundMinimal){
        			System.out.println("Error!");
        			data += "Couldn't find a minimal solution for: \n\n" + alloy.getCurrentSolution().toString() + "\n" + 
        					"-------------------------------------\n";
        			foundError = true;
        			totalErrors++;        			
        		}
        		else
            		System.out.println("OK!");
        			
        		
        		alloy = alloy.next();
        	}
        }
        
    	if(foundError){
    		System.out.println(totalErrors + " inconsistencies were found! Please read the output file for details.");
            try{
        		writeData(optOutput.value, data);
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
	}
	
	private static void writeData(File file, String data) throws IOException{
		FileWriter fstream = new FileWriter(file);
		BufferedWriter out = new BufferedWriter(fstream);
		
		out.write(data);
		
		out.close();
	}
	
	
	private static Set<MinSolution> getIsomorphicSolutions(Set<MinSolution> solutions, Bounds bounds){
		return IsomorphicSolutionBuilder.getIsomorphicSolutions(solutions, bounds);
	}
	
}