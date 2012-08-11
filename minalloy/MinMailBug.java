/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package minalloy;

import java.awt.Toolkit;
import java.awt.datatransfer.StringSelection;
import java.lang.Thread.UncaughtExceptionHandler;
import edu.mit.csail.sdg.alloy4.OurDialog;

/** 
 * Modified heavily from edu.mit.csail.sdg.alloy4.MailBug 
 * to avoid sending _Aluminum_ error reports to the Alloy team.
 * 
 * @author Tim
 *
 */

public final class MinMailBug implements UncaughtExceptionHandler {

   /** Construct a new MinMailBug object. */
   private MinMailBug() { }

   /** Setup the uncaught-exception-handler and use a separate thread to query alloy.mit.edu for latest version number. */
   public static void setup() {
      if (Thread.getDefaultUncaughtExceptionHandler() != null) return;
      MinMailBug x = new MinMailBug();
      Thread.setDefaultUncaughtExceptionHandler(x);     	   
   }

   /** This method concatenates a Throwable's message and stack trace and all its causes into a single String. */
   public static String dump (Throwable ex) {
      StringBuilder sb = new StringBuilder();
      while(ex != null) {
         sb.append(ex.getClass()).append(": ").append(ex.getMessage()).append('\n');
         StackTraceElement[] trace = ex.getStackTrace();
         if (trace!=null) for(int n=trace.length, i=0; i<n; i++) sb.append(trace[i]).append('\n');
         ex = ex.getCause();
         if (ex != null) sb.append("caused by...\n");
      }
      return sb.toString().trim();
   }
   
   private void copyToClipboard(String dump)
   {
	   StringSelection ss = new StringSelection(dump);
	   Toolkit.getDefaultToolkit().getSystemClipboard().setContents(ss, ss);
   }
  
   /** This method is an exception handler for uncaught exceptions. */
   public void uncaughtException (Thread thread, Throwable ex) {
      if (ex != null) {
         System.out.flush();
         System.err.flush();
         System.err.println("Exception: " + ex.getClass());
         System.err.println("Message: " + ex);
         System.err.println("Stacktrace:");
         System.err.println(dump(ex));
         System.err.flush();
      }
      for(Throwable ex2 = ex; ex2 != null; ex2 = ex2.getCause()) {
         if (ex2 instanceof StackOverflowError) OurDialog.fatal(new Object[] {
               "Sorry. Aluminum has run out of stack space.",
               " ",
               "Try simplifying your model or reducing the scope.",
               "And try reducing Options->SkolemDepth to 0.",
               "And try increasing Options->Stack.",
               " ",
               "There is no way for Aluminum to continue execution, so pressing OK will shut down Aluminum."
         });
         if (ex2 instanceof OutOfMemoryError) OurDialog.fatal(new Object[] {
               "Sorry. Aluminum has run out of memory.",
               " ",
               "Try simplifying your model or reducing the scope.",
               "And try reducing Options->SkolemDepth to 0.",
               "And try increasing Options->Memory.",
               " ",
               "There is no way for Aluminum to continue execution, so pressing OK will shut down Aluminum."
         });
      }
      
      final String yes = "Copy to Clipboard", no = "Exit without copying";
      if (OurDialog.yesno(new Object[] {
              "Sorry. A fatal internal error has occurred.",
              " ",
              "Please send email to tn@cs.wpi.edu describing the error below.",
              " ",
              "(Click below to copy the error to your clipboard before exiting Aluminum.)",
              " ",
              dump(ex),
              " "
        }, yes, no)) copyToClipboard(dump(ex));
      
      System.exit(1);
   }   
   
}
