/* This class implements a program that records the execution time of alloy specs.*/



import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

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
import minalloy.translator.MinA4Options;
import minalloy.translator.MinA4Solution;
import minalloy.translator.MinTranslateAlloyToKodkod;

/** This class demonstrates how to access Alloy4 via the compiler methods. */

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
    public static void main(String[] args) throws Err {
    	FileOption optInput = new FileOption("-i");
    	FileOption optOutput = new FileOption("-o");
    	BooleanOption optMinimal = new BooleanOption("-m", true);
    	IntOption optNumberOfModels = new IntOption("-n", 10);
    	
    	CmdLineParser optParser = new CmdLineParser();
    	optParser.addOption(optInput);
    	optParser.addOption(optOutput);
    	optParser.addOption(optMinimal);
    	optParser.addOption(optNumberOfModels);
    	
    	ArrayList<Long> output = new ArrayList<Long>();
    	
    	try{
    		optParser.parse(args);
    	}
    	catch(CmdLineException e){
    		System.err.println(e.getMessage());
    	}

    	if(optInput.value == null)
    		System.err.println("No input file is provided!");
    	if(optInput.value == null)
    		System.err.println("No output file is provided!");    	
    	    	
        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };

        for(String filename:args) {

            // Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking "+filename+" =============");
            Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

            // Choose some default options for how you want to execute the commands
            MinA4Options options = new MinA4Options();

            for (Command command: world.getAllCommands()) {
                // Execute the command
                System.out.println("============ Command "+command+": ============");
                long time = 0;
                time = System.currentTimeMillis();
                MinA4Solution ans = MinTranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
                time = System.currentTimeMillis() - time;

            	System.out.println(ans);
                System.out.println("TIME: " + time);
                output.add(time);
                
                int counter = 1;
                
                while(ans.satisfiable()){
                // Print the outcome
                    time = System.currentTimeMillis();                	
                	ans = ans.next();
                    time = System.currentTimeMillis() - time;
                    
                	System.out.println(ans);
                    System.out.println("TIME: " + time);
                    output.add(time);
                    
                    counter ++;
                }
            }
        }
    }
    
    private void writeOutput(ArrayList<Long> output, File outputFile) throws IOException{
    	FileWriter fstream = new FileWriter(outputFile);
    	
    }
}