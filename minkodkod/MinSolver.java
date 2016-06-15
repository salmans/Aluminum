package minkodkod;

/* 
 * Kodkod -- Copyright (c) 2005-2007, Emina Torlak
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.StringTokenizer;

import javax.swing.JOptionPane;

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.TimeoutException;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import minkodkod.MinSolution.MinimizationHistory;
import minkodkod.engine.fol2sat.*;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;


/** 
 * From Kodkod:
 * A computational engine for solving relational formulae.
 * A {@link kodkod.ast.Formula formula} is solved with respect to given 
 * {@link kodkod.instance.Bounds bounds} and {@link kodkod.engine.config.Options options}.
 * 
 * ALUMINUM: This is a modification of the original Solver that produces minimal models. 
 * A MinSolver can also get consistent-fact sets and augment models with relational-facts 
 * after producing them.  
 * 
 * Note that all solving is done via solveAll(). There is no solve() method implemented, 
 * although one could be; all minimization is currently done in each MinSolutionIterator.
 */
public final class MinSolver {
	private final Options options;
	private final MinExtraOptions extraOptions;	
	
	//The iterator that acquires the SAT solver.
	private MinSolutionIterator activeIterator;
	
	// Option: force SBP to be respected
	public boolean forceRespectSB;

	/**
	 * Constructs a new Solver with the default options and extraOptions.
	 * @effects this.options' = new Options()
	 * @effects this.extraOptions = new MinExtraOptions()
	 */
	public MinSolver() {
		this.options = new Options();
		this.extraOptions = new MinExtraOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * @effects this.options' = options
	 * @effects this.extraOptions = new MinExtraOptions()
	 * @throws NullPointerException - options = null
	 */
	public MinSolver(Options options) {
		if (options == null)
			throw new NullPointerException();
		this.options = options;
		this.extraOptions = new MinExtraOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * @effects this.options' = options
	 * @throws NullPointerException - options = null || extraOptions == null
	 */
	public MinSolver(Options options, MinExtraOptions extraOptions) {
		if (options == null || extraOptions == null)
			throw new NullPointerException();
		this.options = options;
		this.extraOptions = extraOptions;
	}
	
	/**
	 * Returns the Options object used by this Solver
	 * to guide translation of formulas from first-order
	 * logic to cnf.
	 * @return this.options
	 */
	public Options options() {
		return options;
	}

	/**
	 * Returns the MinExtraOptions object used by this Solver to customize the
	 * minimization behavior.
	 * @return this.options
	 */
	public MinExtraOptions extraOptions() {
		return extraOptions;
	}
		
	
	/**
	 * Attempts to find all solutions to the given formula with respect to the specified bounds or
	 * to prove the formula's unsatisfiability.
	 * If the operation is successful, the method returns an iterator over n Solution objects. The outcome
	 * of the first n-1 solutions is SAT or trivially SAT, and the outcome of the nth solution is UNSAT
	 * or tirivally  UNSAT.  Note that an unsatisfiability
	 * proof will be constructed for the last solution iff this.options specifies the use of a core extracting SATSolver.
	 * Additionally, the CNF variables in the proof can be related back to the nodes in the given formula 
	 * iff this.options has variable tracking enabled.  Translation logging also requires that 
	 * there are no subnodes in the given formula that are both syntactically shared and contain free variables.  
	 * 
	 * @return an iterator over all the Solutions to the formula with respect to the given bounds
	 * @throws NullPointerException - formula = null || bounds = null
	 * @throws kodkod.engine.fol2sat.UnboundLeafException - the formula contains an undeclared variable or
	 * a relation not mapped by the given bounds
	 * @throws kodkod.engine.fol2sat.HigherOrderDeclException - the formula contains a higher order declaration that cannot
	 * be skolemized, or it can be skolemized but this.options.skolemize is false.
	 * @throws AbortedException - this solving task was interrupted with a call to Thread.interrupt on this thread
	 * @throws IllegalStateException - !this.options.solver().incremental()
	 * @see Solution
	 * @see Options
	 * @see Proof
	 */
	public Iterator<MinSolution> solveAll(final Formula formula, final Bounds origBounds) 
		throws HigherOrderDeclException, UnboundLeafException, AbortedException {
		if (!options.solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");
						
		MinSolutionIterator iterator = new MinSolutionIterator(this, formula, origBounds, options, extraOptions);
		
		return iterator;
	}
	
	/**
	 * Augments a model from an iterator with a set of facts
	 * @param formula the original FOL formula.
	 * @param origBounds the bounds.
	 * @param iterator the previous iterator.
	 * @param solution the current solution of the previous iterator being augmented.
	 * @param augmentWith the facts to augment.
	 * @return a new iterator over the augmented models.
	 * @throws MinHigherOrderDeclException
	 * @throws UnboundLeafException
	 * @throws AbortedException
	 */
	//TODO in a refined implementation, we don't need the formula and bound since we have the translation 
	//via previous iterator.
	public MinSolutionIterator augment(final Formula formula, Iterator<MinSolution> prevIterator, 
			Instance augmentWith)
			throws HigherOrderDeclException, UnboundLeafException, AbortedException, ExplorationException {
		
		if (!options.solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");
		
		MinSolutionIterator msiterator = (MinSolutionIterator)prevIterator;
		
		if(msiterator.trivial)
		{
			// Disable augmentation and redirect them to the set of consist. facts (for now):
			JOptionPane.showMessageDialog(null, "The spec given was trivially satisfiable, and so it had only one minimal model (shown),\n"+
			"to which any relational fact in the set of consistent facts may be added without consequence.\n\n"+
					"Explicit exploration is unavailable.");
			return msiterator;
		}
		
		// If this iterator never produced a model
		if(msiterator.lastSatSolutionFound == null && !msiterator.hasNext())
		{
			// Error
			throw new ExplorationException("Attempted to augment without a model.");
		}
		
		// Augmenting is always performed on skolemBounds.
		Bounds skBounds = ((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds;
		
		ArrayList<Integer> allAugments = new ArrayList<Integer>();
		
		// Do not use getLastSolution() here: it may be the iterator is empty, in which case it would contain no
		// propositional model, being the UNSAT soln. Instead, use the last *instance* found:	
		Map<Relation, TupleSet> solutionTuples = msiterator.lastSatSolutionFound.instance().relationTuples();
		Map<Relation, TupleSet> augmentTuples = augmentWith.relationTuples();

		for(Relation r : solutionTuples.keySet()){
			TupleSet tuples = solutionTuples.get(r);
			for(Tuple t: tuples){
				int index = MinTwoWayTranslator.getPropVariableForTuple(skBounds, msiterator.getTranslation(), r, t);
				//if there is no primary variables assigned to this relation, continue.
				if(index == -1)
					continue;
				allAugments.add(index);
			}
		}
		
		for(Relation r : augmentTuples.keySet()){
			TupleSet tuples = augmentTuples.get(r);
			if(tuples != null)
				for(Tuple t: tuples){
					if(solutionTuples.get(r).contains(t))
						throw new ExplorationException("The fact " + t + " is already true in the solution.");

					int index = MinTwoWayTranslator.getPropVariableForTuple(skBounds, msiterator.getTranslation(), r, t);					
					//if there is no primary variables assigned to this relation, continue.
					if(index == -1)
						continue;
					
					allAugments.add(index);
				}
		}
		
		// We want the same MinSolver, because MinSolver governs
		// the active iterator and allows the iterators to share the SAT solver.
		MinSolutionIterator iterator = new MinSolutionIterator(this, formula, skBounds, options, extraOptions, allAugments, msiterator);
				
		return iterator;
	}	
	
	/**
	 * Returns the consistent facts for the current model loaded in the given iterator.
	 * @param iterator the iterator.
	 * @return the consistent facts tuple relations of an instance.
	 * @throws TimeoutException
	 * @throws ContradictionException
	 */
	public Instance getConsistentFacts(Iterator<MinSolution> iterator) throws TimeoutException, ContradictionException{
		MinSolutionIterator theIterator = (MinSolutionIterator)iterator;
				
		if(theIterator.trivial)
		{
			// No translation available to augment. Get the upper bounds - the lower bounds:
			Bounds skBounds = ((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds;			
			Instance results = new Instance(skBounds.universe());			
			for(Relation r : skBounds.relations())
			{				
				TupleSet tuples = skBounds.upperBound(r).clone();			
				tuples.removeAll(skBounds.lowerBound(r));							
				results.add(r, tuples);							
			}
			
			//JOptionPane.showMessageDialog(null, "getConsistentFacts: "+results);			
			return results;
		}

		// If not trivial, go through the propositional translation
		return MinTwoWayTranslator.translatePropositions(
				theIterator.translation, ((MinReporterToGatherSkolemBounds)theIterator.options.reporter()).skolemBounds,
				theIterator.mapVarToRelation,
				theIterator.getConsistentFacts()); 
	}
	
	/**
	 * Returns a list of consistent facts for the current model loaded in the given iterator as 
	 * a line separated string.
	 * @param iterator the iterator.
	 * @return returns a list of line separated strings of consistent facts. If an exception occurs,
	 * it returns an empty string.
	 */    
	public String getCFList(Iterator<MinSolution> iterator){
		return getCFList(iterator, null, null);
	}	
	
	/**
	 * Returns a list of consistent facts for the current model loaded in the given iterator as 
	 * a line separated string. This is used by min*ALLOY*, not minkodkod.
	 * 
	 * Alloy can actually rename an atom *twice* -- e.g., Kodkod may have an atom Object$2 that
	 *   gets renamed as Conference$2 before being renamed for _display_ as Conference1. Hence
	 *   why we pass two dictionaries. The first maps from Alloy original name to display name;
	 *   the second maps from Kodkod name to Alloy original name.
	 * 
	 * @param iterator the iterator.
	 * @param dictionary Alloy original names mapped to Alloy display names
	 * @param atom2name Kodkod names mapped to Alloy original names
	 * @return returns a list of line separated strings of consistent facts. If an exception occurs,
	 * it returns an empty string.
	 */    
	public String getCFList(Iterator<MinSolution> iterator, Map<String, String> dictionary, Map<Object, String> atom2name){
		String retVal = "";
		MinSolutionIterator miniterator = ((MinSolutionIterator)iterator);
		MinTranslation translation = miniterator.translation;	
		
		Bounds bounds = ((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds;
		
		// Keeps the pattern of the output when a NEW is involved. The outputs that have
		// repetitive patterns will be discarded.
		Set<String> uniqueOutputPattern = new LinkedHashSet<String>();
		
		Instance consistentFacts = null;
		
		try{
			consistentFacts = getConsistentFacts(iterator);
		}
		catch(Exception e){
			return "";
		}
		
		Map<Relation, TupleSet> cfTuples = consistentFacts.relationTuples();

		// For each relational fact in the set, construct a descriptive string.
		for(Relation r : cfTuples.keySet()){
			TupleSet tuples = cfTuples.get(r);
			for(Tuple t: tuples){
				if(!miniterator.trivial)
				{
					int index = MinTwoWayTranslator.getPropVariableForTuple(bounds, translation, r, t);
					// if there are no primary variables assigned to this relation, continue.
					if(index == -1)
						continue;
				}
				
				retVal += augmentTupleToString(r, t, dictionary, atom2name, uniqueOutputPattern);
				
			} // end each tuple for this relation in CFs
		} // end for each relation in CFs
		
		return retVal;
	}

	private String augmentTupleToString(Relation r, Tuple t,
			Map<String, String> dictionary, Map<Object, String> atom2name,
			Set<String> uniqueOutputPattern)
	{
		if(dictionary != null && atom2name != null)
		{
			// Construct a more sensible list than just the raw tuples.
			
	        final StringBuilder ret = new StringBuilder("["); //This section of the code produces t.toString manually:
	        StringBuilder pattern = new StringBuilder("["); //keeps the pattern of the next output.
	        	        
	        //////////////////////////////////////////////////
	        // Construct the list of Alloy original names for the Kodkod atom names:
	        List<String> alloyOrig = new ArrayList<String>(t.arity());
	        for(int ii=0;ii<t.arity();ii++)
	        {
	        	Object kodkodAtom = t.atom(ii);
	        	if(atom2name.containsKey(kodkodAtom))
	        		alloyOrig.add(atom2name.get(kodkodAtom));
	        	else
	        		alloyOrig.add(kodkodAtom.toString());
	        }
	        	        
	        ////////////////////////////////////////////////// 
	        
	        // To make sure no repeats of identical (up to choice of new atom) augmentation string,
	        // pattern removes the labels from ret.	        
	        
	        // For each atom in the tuple:	        	        
	        String label = "";	        
	        boolean first = true;
	        for (int i = 0; i < t.arity(); i++) {
	        	if(!first) 
	        	{
	        		ret.append(", ");
	        		pattern.append(",");
	        	}
        		first = false;

	            label = dictionary.get(alloyOrig.get(i));
	            if(label != null){
	            	ret.append(label);
	            	pattern.append(label);
	            }
	            else{
	            	// If the labeling failed, use the raw atom name:
	            	ret.append("NEW(" + t.atom(i) + ")");
	            	pattern.append("NEW");
	            }
	        }
	        
	        ret.append("]");
	        pattern.append("]");
	        	        
	        if(uniqueOutputPattern.add(r.toString()+ pattern.toString())){ //if the pattern is not repetitive
	        	String relationName = r.toString();
	        	if(relationName.startsWith("this/"))	//Drop this from the beginning of the relations.
	        		relationName = relationName.substring(5);
	        	return relationName + ret.toString() + "\n";
	        }
	        else
	        	return "";
		} 
		
		// No dictionary/dictionaries, so default to the raw tuple:
		return r.toString() + t.toString() + "\n";		
	}

	/**
	 * Builds a consistent fact that can be used for augmenting a model.
	 * This is used by min*ALLOY*, not minkodkod.
	 * @param inputStr the input string
	 * @param iterator the iterator to be augmented by this fact.
	 * @return an object of type Instance containing the augmenting fact.
	 * @throws ExplorationException
	 */	
	public Instance parseString(String inputStr, Iterator<MinSolution> iterator) throws ExplorationException{
		return parseString(inputStr, iterator, null, null);
	}	
	
	/**
	 * Builds a consistent fact that can be used for augmenting a model.
	 * This is used by min*ALLOY*, not minkodkod.
	 * @param inputStr the input string
	 * @param iterator the iterator to be augmented by this fact.
	 * @param display2orig is used to translate the atoms to their names in Kodkod.
	 * @return an object of type Instance containing the augmenting fact. 
	 * @throws ExplorationException 
	 */
	public Instance parseString(String inputStr, Iterator<MinSolution> iterator, Map<String, String> display2orig, Map<Object, String> atom2name) throws ExplorationException {
		inputStr = inputStr.trim();
		//inputStr = inputStr.replaceAll(" ", "");				
		
		String relationName = null;
		int index1 = inputStr.indexOf('[');
		if(index1 == -1)
			throw new ExplorationException("Augmentation string did not contain a `[`"+relationName);
		
		relationName = inputStr.substring(0, index1);

		int index2 = inputStr.indexOf(']');
		if(index2 == -1)
			throw new ExplorationException("Augmentation string must end with `]`"+relationName);
		
		// Extract a string for each component of the tuple
		StringTokenizer tokenizer = new StringTokenizer(inputStr.substring(index1 + 1, index2), ",");		
		ArrayList<String> stringComponentsGiven = new ArrayList<String>();		
		while(tokenizer.hasMoreTokens()){
			stringComponentsGiven.add(tokenizer.nextToken().trim());
		}

		Bounds bounds = ((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds;
		
		Set<Relation> relations = bounds.relations();
		Relation relation = null;
		for(Relation r: relations){
			if(r.name().equals(relationName) || r.name().equals("this/" + relationName)){
				relation = r;
				break;
			}
		}
		
		// If no relation found for this name		
		if(relation == null) 
			throw new ExplorationException("No relation found with name "+relationName);
		
		TupleSet tuples = bounds.upperBound(relation);
		// If no tuples found (bound doesn't exist)
		if(tuples == null)
			throw new ExplorationException("No upper bound given for "+relationName);

		//String debug = "dictionary: "+display2orig+"\natom2name:"+atom2name+"\n"+
		//"components given: "+stringComponentsGiven+"\n";
		
		// Find the tuple in R's upper bound that matches the string
		// Check for *each* tuple in the upper bound: is it a match?
		Tuple tuple = null;
		for(Tuple t: tuples)
		{
			boolean found = true;
			
			//debug += "  checking: "+t+"\n";
			
			// Find a match for each component of the tuple
			for(int i = 0; i < t.arity(); i++)
			{
				String stringComponentToMatch = stringComponentsGiven.get(i); 
				
				if(display2orig != null && atom2name != null)
				{		
					// atom2name maps Kodkod atoms to their "original" Alloy strings.
					// display2orig maps Alloy display strings to their "original" strings.
					
					// Get the original name for this candidate atom
					Object kodkodAtom = t.atom(i);
					String alloyOrigName;
					if(atom2name.containsKey(kodkodAtom))
						alloyOrigName = atom2name.get(kodkodAtom);
					else
						alloyOrigName = kodkodAtom.toString();
					
					// Get the original name for the desired atom
					String desiredOrigName = "";					
					if(display2orig.containsKey(stringComponentToMatch))
						desiredOrigName = display2orig.get(stringComponentToMatch);
					else
						desiredOrigName = ""; // flag for case 2
							
					//debug += "desiredOrigName="+desiredOrigName+"\n";
					//debug += "alloyOrigName="+alloyOrigName+"\n";
					//debug += "eq: "+desiredOrigName.equals(alloyOrigName)+"\n";
					
					// Case 1: we had a (reverse) display mapping for this desired atom
					if(desiredOrigName.length() > 0)
					{ 
						if(!desiredOrigName.equals(alloyOrigName))
						{
							found = false;
							break;
						}
					}
					// Case 2: must be a new instance
					else
					{
						if(!("NEW(" + t.atom(i) + ")").toString().equals(stringComponentToMatch)){
							found = false;
							break;
						}
					}
				}
				// No mapping of names given: need to match exactly
				else 
				{
					if(!t.atom(i).toString().equals(stringComponentToMatch)){
						found = false;
						break;
					}
				}
			} // end for each element of the tuple
			
			if(found == true){
				tuple = t;
				break;
			}
		}
		
		//JOptionPane.showMessageDialog(null, debug);
		
		if(tuple == null) //There is no such tuple
			throw new ExplorationException("No matching tuple found for the given augmentation string: "+inputStr);

		Instance retVal = new Instance(bounds.universe());
		retVal.add(relation, bounds.universe().factory().setOf(tuple));				
		
		return retVal;
	}
	
	
	/**
	 * Returns the bounds after skolemization.
	 */
	public Bounds getSkolemBounds(){
		return ((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds;
	}
	
	/**
	 * {@inheritDoc}
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return options.toString();
	}
	
	/**
	 * Returns the result of solving an unsat formula.
	 * @param translation the translation 
	 * @param stats translation / solving stats
	 * @return the result of solving an unsat formula.
	 */
	private static MinSolution unsat(MinTranslation translation, MinStatistics stats) {
		//final SATSolver cnf = translation.cnf();
		//final TranslationLog log = translation.log();
		// Never instanceof SATProver in aluminum
		//if (cnf instanceof SATProver && log != null) {
		//	return MinSolution.unsatisfiable(stats, new ResolutionBasedProof((SATProver) cnf, log), null, null);
		//} else { // can free memory
			final MinSolution sol = MinSolution.unsatisfiable(stats, null, null, null);
			//cnf.free();
			return sol;
		//}
	}	
	
	/**
	 * Returns a proof for the trivially unsatisfiable log.formula,
	 * provided that log is non-null.  Otherwise returns null.
	 * @requires log != null => log.formula is trivially unsatisfiable
	 * @return a proof for the trivially unsatisfiable log.formula,
	 * provided that log is non-null.  Otherwise returns null.
	 */
	private static Proof trivialProof(TranslationLog log) {
		return log==null ? null : new TrivialProof(log);
	}
	
	/**
	 * "Pads" the argument instance with the mappings that occur in bounds.lowerBound
	 * but not in the instance. 
	 * @requires instance.relations in bounds.relations
	 * @effects instance.relations' = bounds.relations' &&
	 *          instance.tuples' = bounds.lowerBound ++ instance.tuples
	 * @return instance
	 */
	private static Instance padInstance(Instance instance, Bounds bounds) {
		for (Relation r : bounds.relations()) {
			if (!instance.contains(r)) {
				instance.add(r, bounds.lowerBound(r));
			}
		}
		for (IntIterator iter = bounds.ints().iterator(); iter.hasNext();) {
			int i = iter.next();
			instance.add(i, bounds.exactBound(i));
		}
		return instance;
	}

	/**
	 * Creates an instance from the given Bounds.  The instance
	 * is simply the mapping bounds.lowerBound.
	 * @return the instance corresponding to bounds.lowerBound
	 */
	private static Instance toInstance(Bounds bounds) {
		final Instance instance = new Instance(bounds.universe());
		for (Relation r : bounds.relations()) {
			instance.add(r, bounds.lowerBound(r));
		}
		for (IntIterator iter = bounds.ints().iterator(); iter.hasNext();) {
			int i = iter.next();
			instance.add(i, bounds.exactBound(i));
		}
		return instance;
	}
	
	/**
	 * An iterator over all solutions of a model.
	 * @author Emina Torlak
	 */
	public static final class MinSolutionIterator implements Iterator<MinSolution> {
		private final Options options;
		private final MinExtraOptions extraOptions;
		
		private Formula formula;
		
		/**
		 * The original, pre-Skolem bounds passed to Kodkod.
		 * Access the post-Skolem bounds via MyReporter.
		 */
		private Bounds origBounds;
		
		private boolean trivial = false;
		
		private MinTranslation translation;
		private Map<Integer, Relation> mapVarToRelation;
		private long translTime;
		private MinSolution lastSolution;
		
		//the MinSolver instance that creates the iterator.
		private final MinSolver minSolver;
		
		//Modifications for minimal models
		private Boolean sat = null;
		private MinSolution unsatSolution = null;
		
		/** 
		 * Augmentation requires we keep a handle on the last instance found
		 * even if the iterator is now empty (i.e., lastSolution = an unsatisfiable result).
		 */
		public MinSolution lastSatSolutionFound = null;
		
		/**
		 * Keeps cone restriction clauses such that the next model from the SATsolver
		 * is not in any of the previous cones.
		 */
		private Set<Set<Integer>> coneRestrictionClauses = new HashSet<Set<Integer>>();
		/**
		 * Keeps a list of all the constraints that are being taken into account.
		 * Some operations such as getConsistentFacts() has to eliminate all the constraints.
		 * Also, when another iterator is using the solver, the constraints from
		 * the current iterator should be removed.
		 */
		private Set<IConstr> coneRestrictionConstraints = new HashSet<IConstr>();

		/**
		 * Keeps a list of all the unit constraints due to a bug in SAT4J that does not
		 * return a handle to remove unit constraints.
		 */
		private Set<Integer> coneRestrictionUnits = new HashSet<Integer>();
		
		/**
		 * The augments for this iterator.
		 */
		private final int[] augments;
		
		/**
		 * Constructs a solution iterator for the given formula, bounds, and options.
		 */
		MinSolutionIterator(MinSolver minSolver, Formula formula, Bounds origBounds, Options options, MinExtraOptions extraOptions) {			
			this(minSolver, formula, origBounds, options, extraOptions, null, null);			
		}

		/**
		 * For debugging
		 */
		long parentHash = 0;
		
		/**
		 * Constructs a solution iterator for the given formula, bounds, options and augmentations.
		 * @param formula
		 * @param origBounds
		 * @param options
		 * @param augs
		 * @param prevIterator
		 */
		
		MinSolutionIterator(MinSolver minSolver, Formula formula, Bounds origBounds, Options options, MinExtraOptions extraOptions, 
				ArrayList<Integer> augs, MinSolutionIterator prevIterator) {
			this.minSolver = minSolver;
			this.formula = formula;
			this.origBounds = origBounds;
			this.options = options;
			this.extraOptions = extraOptions;
			this.translation = null;
			this.augments = (augs == null) ? null : toIntCollection(augs);					
			
			if(prevIterator != null){  //if augmenting on a previous iterator
				this.translation = prevIterator.getTranslation();
				this.mapVarToRelation = prevIterator.mapVarToRelation;		
				this.parentHash = prevIterator.hashCode();
			}
		}
		
		/**
		 * Debugging string.
		 */
		public String toString()
		{
			StringBuffer result = new StringBuffer();
			result.append("Iterator hash code:"+hashCode()+"\n");
			result.append("Iterator parent's hash code:"+parentHash+"\n");
			result.append("Iterator formula:"+formula+"\n");
			result.append("Iterator origBounds:"+origBounds+"\n");
			result.append("Iterator augmentations:"+Arrays.toString(augments)+"\n");
			result.append("Iterator translation's num pri vars:"+translation.numPrimaryVariables()+"\n");
			result.append("Iterator solver's hash code:"+minSolver.hashCode()+"\n");
			result.append("Iterator mapVarToRelation:"+mapVarToRelation+"\n");
			return result.toString();
		}
		
		/**
		 * Returns true if there is another solution.
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			// Can no longer set formula=null; instead use unsatSolution (reversed)
			return (unsatSolution == null);
		}
		
		/**
		 * Solves translation.cnf and adds the negation of the
		 * found model to the set of clauses.
		 * @requires this.translation != null
		 * @effects this.translation.cnf is modified to eliminate
		 * the  current solution from the set of possible solutions
		 * @return current solution
		 */
		private MinSolution nonTrivialSolution() {						
			try {
				final MinSATSolver internalSolver = translation.cnf();
				
				try{
					// If all the previous constraints have been removed by another operation,
					// add them again.
					if(coneRestrictionConstraints.isEmpty()){
						addAllClauses();
					}
				}
				catch(ContradictionException e){
					JOptionPane.showMessageDialog(null, "CONTRADICTION exception in nonTrivialSolution()");
				}
				
				////////////////////////////////////////////////////////
				options.reporter().solvingCNF(translation.numPrimaryVariables(), internalSolver.numberOfVariables(), internalSolver.numberOfClauses());				
				final long startSolve = System.currentTimeMillis();				
				boolean isSat = false;				

				//System.out.println("Finding a non trivial solution...");
				
				// This populates a MINIMAL model in lastModel, NOT the candidate
				boolean respectsSB = false;							
				
				// If a model found, need to add constraints to forbid its cone.
				// Possibly add more sets of CR clauses if SBP must be respected					
				do {
					// Get the next minimal model, if any				
					isSat = solve();

					if(isSat) 
					{					
						final int primary = translation.numPrimaryVariables();					
						final Set<Integer> notModel = new HashSet<Integer>();		
						
						respectsSB = translation.satisfiesSBP(translation.cnf().getLastModel());						
						/*if(minSolver.forceRespectSB)
						{							
							System.out.println("Must respect SB. Result: "+respectsSB);													
						}*/
						
						// Negate this model's positive diagram. 
						// We will use this disjunctively for "cone-restriction": preventing models 
						// (or any of their supermodels) from occurring again.
						for(int i = 1; i <= primary; i++){
							if(internalSolver.valueOf(i)){
								notModel.add(-i);
							}
						}
																								
						try{	
							//JOptionPane.showMessageDialog(null, translation.permutations);
							// Add the cone restriction for this model:
							addConeRestriction(notModel, internalSolver);
							// Add the cone restriction for all (safe) adjacent transpositions.
							// (If forcing results to respect SBP, this function needs to make sure it doesn't add a cone-restriction clause
							// for SBP-respecting solutions, or it risks preventing us from seeing the canonical soln we need.) 							 							
							addPermConeRestrictions(notModel, internalSolver);
						}
						catch(ContradictionException e) {
							// This iterator is now out of models. Either we just gave the empty model,
							// or a cone restriction clause has resulted in a contradiction. So make sure
							// that this iterator never yields a model again:
							JOptionPane.showMessageDialog(null, "Contradiction; out of models. Augmentation will be disabled.");
							//final long endSolveU = System.currentTimeMillis();				
							//final MinStatistics statsU = new MinStatistics(translation, translTime, endSolveU - startSolve);
							//unsatSolution = unsat(translation, statsU);	
							// But still return the model we generated
						}
																
						// Keep going until we either run out of models or find one that respects the SBP  
					}
				} while(isSat && minSolver.forceRespectSB && !respectsSB);											
			
			final long endSolve = System.currentTimeMillis();				
			final MinStatistics stats = new MinStatistics(translation, translTime, endSolve - startSolve);
				
			if(isSat) {
				/////////////////////////////////////////////
				// Found a minimal model: report it				
				int[] minPropositionalModel = translation.cnf().getLastModel().clone();
				MinReporterToGatherSkolemBounds reporter = (MinReporterToGatherSkolemBounds)options.reporter();
				MinimizationHistory history = null;
				if(extraOptions.logMinimizationHistory())
					history = new MinimizationHistory(reporter.getIterations(), reporter.getReducedElements(), 
							reporter.getReducedAttributes(), reporter.getReducedRelations());
				
				//////////////////////////////////////////
				// Does this solution satisfy the SBP?
				// If not, flag this solution as spurious (we're guaranteed to get an isomorph either before or after)
				boolean isCanonical = translation.satisfiesSBP(minPropositionalModel);										
					
				////////////////////////////////////////
				// extract the current solution; can't use the sat(..) method because it frees the sat solver
				final MinSolution sol = 
						MinSolution.satisfiable(stats, padInstance(translation.interpret(), origBounds), 
								                history, minPropositionalModel, isCanonical);
				return sol;				
			}
			else {
				//////////////////////////////////////
				// No viable solution remaining
				unsatSolution = unsat(translation, stats); 
				return unsatSolution;
			}
		} catch (SATAbortedException sae) {
			throw new AbortedException(sae);
		}				
	}
				
		/**
		 * Add a clause for this negated positive-diagram.
		 * 
		 * @param notModel
		 * @param internalSolver
		 * @throws ContradictionException
		 */
		private void addConeRestriction(Set<Integer> notModel, MinSATSolver internalSolver)
				throws ContradictionException
		{						
			// It is vital that notModel be a SET, not a LIST (the literals can be transposed).
			
			if(notModel.size() == 1)
			{
				// No risk of adding duplicates; it's just a set.
				for(int unit : notModel)
					coneRestrictionUnits.add(unit);
			}
			else
			{				
				// Avoid adding duplicate clauses to the *SAT SOLVER*. Adding duplicate 
				// clauses ought to be idempotent, but it is not: the same IConstr
				// is returned, and removeConstraint will only end up removing the 
				// *FIRST* such clause, not all of them. So never add duplicates!
				if(coneRestrictionClauses.contains(notModel))
					return;								
				
				// (This will be called if notModel.size() ==0, triggering the exception.)							
				coneRestrictionConstraints.add(internalSolver.addConstraint(toIntCollection(notModel)));
				coneRestrictionClauses.add(notModel);
								
			}			
		}
		
		/**
		 * Add cone-restriction clauses for the broken symmetries (i.e., the symmetries for which
		 * Kodkod produces a symmetry-breaking predicate) of this negated positive-diagram.
		 * 
		 * @param notModel
		 * @param internalSolver
		 * @throws ContradictionException
		 */
		private void addPermConeRestrictions(Set<Integer> notModel, MinSATSolver internalSolver) 
				throws ContradictionException
		{			
			// the CALLER is responsible for adding the original restriction clause:
			//addConeRestriction(notModel, internalSolver);
			
			
			
			int permCounter = 0;
			for(Map<Integer, Integer> aPerm : translation.permutations)
			{
				// For safety. Note that this is a *completely different use*
				// of the symmetry-breaking option. Here it means the number of
				// permuted cone-restriction clauses. In the SBP, it limits
				// the *length* of each sub-formula.
				if(permCounter >= options.symmetryBreaking())
					break;				
								
				// Apply this permutation and add the permuted C.R. clause. The permutation
				// is assumed to be complete. I.e., if 2->3, then 3->x for some x. In our
				// case, the permutations are always length 2 (2->3 then 3->2). 
				Set<Integer> permNotModel = permuteNegatedPositiveDiagram(notModel, aPerm);												
				
				// Does this permutation get us to a canonical model? Then don't rule it out!
				// TODO: really we should cache it somehow
				if(minSolver.forceRespectSB && translation.negationSatisfiesSBP(permNotModel)) {
					//System.out.println("negation satisfies SBP and forceRespectSB = true. Continuing to avoid missing a canonical solution.");
					continue;
				}

				addConeRestriction(permNotModel, internalSolver);								
				permCounter++;								
				//System.out.println("Added perm. cone restriction "+permCounter);
				//JOptionPane.showMessageDialog(null, permCounter+" Added restriction. notModel="+notModel+"\naPerm="+aPerm+"\npermNotModel="+permNotModel);				
			}			
		}

		/**
		 * Given a negated positive diagram, apply a permutation to it.
		 * We do NOT need an ordering on the diagram. The order of literals shouldn't matter.
		 * @param notModel
		 * @param aPerm
		 * @return
		 */
		private Set<Integer> permuteNegatedPositiveDiagram(Set<Integer> notModel,
				Map<Integer, Integer> aPerm) 
		{
			Set<Integer> result = new HashSet<Integer>(notModel.size());
			for(Integer aLiteral : notModel)
			{
				if(aLiteral > 0 && aPerm.containsKey(aLiteral))
					result.add(aPerm.get(aLiteral));
				else if(aLiteral < 0 && aPerm.containsKey(aLiteral*-1))
					result.add(aPerm.get(aLiteral*-1)*-1);
				else
					result.add(aLiteral);					
			}
			
			return result;
		}

		/**
		 * Packages the information from the given trivial formula exception
		 * into a solution and returns it.  If the formula is satisfiable, 
		 * this.formula and this.bounds are modified to eliminate the current
		 * trivial solution from the set of possible solutions.
		 * @requires this.translation = null
		 * @effects this.formula and this.bounds are modified to eliminate the current
		 * trivial solution from the set of possible solutions.
		 * @return current solution
		 */
		private MinSolution trivialSolution(TrivialFormulaException tfe) {
			final MinStatistics stats = new MinStatistics(0, 0, 0, translTime, 0);
			
			// Heavily modified from original. When presenting only minimal models,
			// only the first trivial solution needs to be presented: the lower-bounds
			// give a unique (up to isomorphism) minimal model. So return it, but do
			// not prepare other solutions.
			
			trivial = true;
			
			if (tfe.value().booleanValue()) {				
				final Bounds translBounds = tfe.bounds();
				final Instance trivialInstance = padInstance(toInstance(translBounds), origBounds);
				final MinSolution sol = MinSolution.triviallySatisfiable(stats, trivialInstance, null, null);
				
				// Disallow future solving via this iterator.
				unsatSolution = MinSolution.triviallyUnsatisfiable(stats, null, null, null);
				return sol;
			} else {
				unsatSolution = MinSolution.triviallyUnsatisfiable(stats, trivialProof(tfe.log()), null, null);
				return unsatSolution;
			}
		}
		/**
		 * Returns the next solution if any.
		 * @see java.util.Iterator#next()
		 */
		public MinSolution next() {
			if (!hasNext()) return unsatSolution;
			
			//System.out.println("Calling next()...");
			
			claimSATSolver();

			if (translation==null) {
				try {
					translTime = System.currentTimeMillis();
					translation = MinTranslator.translate(formula, origBounds, options);
					translTime = System.currentTimeMillis() - translTime;
					
					//We use this data structure for translation:
					//mapVarToRelation = MinTwoWayTranslator.buildVarToRelationMap(translation, bounds);
					mapVarToRelation = MinTwoWayTranslator.buildVarToRelationMap(translation, 
							((MinReporterToGatherSkolemBounds)options.reporter()).skolemBounds);
					
					// Print the translation (DEBUG ONLY!)
					//String transStr = MinTwoWayTranslator.printTranslation(translation, 
					//		((MyReporter)options.reporter()).skolemBounds,
					//		mapVarToRelation);
					//JOptionPane.showMessageDialog(null, transStr);
					
					setLastSolution(nonTrivialSolution());
				} catch (TrivialFormulaException tfe) {
					translTime = System.currentTimeMillis() - translTime;
					setLastSolution(trivialSolution(tfe));
				} 
			} else {
				setLastSolution(nonTrivialSolution());
			}						
				
			return getLastSolution();
		}

		/**
		 * Prepares the solver to be used by the current iterator.
		 */
		private void claimSATSolver() {
			
//			if(translation != null)
				//JOptionPane.showMessageDialog(null, "before claim: "+((MinSATSolver)translation.cnf()).printConstraints());

			
			if(minSolver.activeIterator != null && minSolver.activeIterator != this)
			{
				//Remove all the constraints of the previous active iterator.
				minSolver.activeIterator.removeAllConstraints();
				//Add the constraints of the current iterator.
				try{
					if(coneRestrictionConstraints.isEmpty())
						addAllClauses();
				}
				catch(ContradictionException e){
					JOptionPane.showMessageDialog(null, "CONTRADICTION exception in claimSATSolver()");
				}
			}
			//if(translation != null)
			//	JOptionPane.showMessageDialog(null, "after claim: "+((MinSATSolver)translation.cnf()).printConstraints());
			
			//Set the activeIterator
			minSolver.activeIterator = this;
			
			//Deactivate SBP if the iterator is augmented by some fact.
			if(translation != null){
				if(isAugmented()) //if the iterator is an augmentation
					((MinSATSolver)translation.cnf()).deactivateSBP();
				else
					((MinSATSolver)translation.cnf()).activateSBP();
			}
		}		
		
		/**
		 * @see java.util.Iterator#remove()
		 */
		public void remove() {
			throw new UnsupportedOperationException();
		}
		
		/**
		 * Prepares a minimal model. May not respect SBP.
		 * @return true if there is a next solution; otherwise, false.
		 * @throws NotMinimalModelException 
		 */
		private boolean solve() {
			// In case this iterator should never return a model again:
			if(!hasNext()) return false;
			
			try{
				Set<Integer> allUnits = new HashSet<Integer>();
				allUnits.addAll(toSet(augments));
				allUnits.addAll(coneRestrictionUnits);
								
				if(allUnits.size() == 0)
					sat = Boolean.valueOf(translation.cnf().solve());
				else
					sat = Boolean.valueOf(translation.cnf().solve(toIntCollection(allUnits)));
		
				//	JOptionPane.showMessageDialog(null, sat+" "+allUnits.size());
				
				if(sat) {	
					try {
						minimize();
					}
					catch(ContradictionException e)
					{
						JOptionPane.showMessageDialog(null, "CONTRADICTION exception in minimize() call");
					}
				}		
										
				return sat;
			} catch (org.sat4j.specs.TimeoutException e) {
				throw new RuntimeException("timed out");
			}
		}

		/**
		 * Minimizes the model in the SAT solver.
		 * @throws TimeoutException
		 * @throws ContradictionException
		 * @throws NotMinimalModelException 
		 */
		private void minimize() throws TimeoutException, ContradictionException
		{
			boolean logDifference = extraOptions.logMinimizationHistory();
			
			int[] modelBeforeMinimization = null;
			int[] modelAfterMinimization = null;			
			// Assumption: Have already found a model at this point!							
			
			// This keeps constraints to be removed from the solver
			// after finding the next model.
			Set<IConstr> constraints = new HashSet<IConstr>();
			
			// All the unit clauses being passed to the solver as assumptions.
			Set<Integer> unitClauses = toSet(augments);						
			
			// Add all coneRestrictionUnits
			for(Integer value: coneRestrictionUnits)
				unitClauses.add(value);
			
			MinSATSolver theSolver = ((MinSATSolver)translation.cnf());						
			//if(logDifference)		
				modelBeforeMinimization = theSolver.getLastModel().clone();
			
			theSolver.deactivateSBP();
			
			int iterationCounter = 1;						
			
			do
			{
				// Given that candidate for minimal-model, try to make something smaller.
				// add: disjunction of negations of all positive literals in M (constraint)
				// add: all negative literals as unit clauses
				
				// [MAX] loseSomethingPositive -> loseSomethingNegative
				
				// An array of the next constraint being added.
				List<Integer> loseSomethingNegative = new ArrayList<Integer>();
				
				int numPrimaryVariables = translation.numPrimaryVariables();
					
				for(int i = 1; i <= numPrimaryVariables; i++){
					if(theSolver.valueOf(i) == false)
						loseSomethingNegative.add(i);
					else // don't set anything curr. negative to positive.
						unitClauses.add(i);
				}
				
				if(loseSomethingNegative.size() == 0)
				{
					// We have minimized down to the empty model. 
					// Avoid calling the final SAT (would be adding the empty clause)
					break;
				}
				if(loseSomethingNegative.size() == 1)
				{
					// We have only one relational fact that can possibly be removed.
					unitClauses.add(loseSomethingNegative.get(0));
				}
				else
				{
					constraints.add(theSolver.addConstraint(toIntCollection(loseSomethingNegative)));
				}
				
				iterationCounter++;
			}
			while(Boolean.valueOf(theSolver.solve(toIntCollection(unitClauses))));

			if(logDifference){
				modelAfterMinimization = theSolver.getLastModel().clone();
				computeDifference(modelBeforeMinimization, modelAfterMinimization);
			}
			
			((MinReporterToGatherSkolemBounds)options.reporter()).setIterations(iterationCounter);
						
			if(!isAugmented()) //if the iterator is NOT an augmentation, activate SBP.
				theSolver.activateSBP();
			
			// Remove all the (non-unit) loseSomethingPositive constraints we just added from the solver:
			Iterator<IConstr> it = constraints.iterator();
			while(it.hasNext()){
				theSolver.removeConstraint(it.next());		
			}
		}

		/**
		 * This method computes the differences between the two propositional models before and after minimization and updates
		 * the reporter accordingly.
		 * @param modelBeforeMinimization the propositional model before minimization.
		 * @param modelAfterMinimization the propositional model after minimization.
		 */
		private void computeDifference(int[] modelBeforeMinimization, int[] modelAfterMinimization){
			int reducedElements = 0;
			int reducedAttributes = 0;
			int reducedRelations = 0;
			
			MinReporterToGatherSkolemBounds reporter = (MinReporterToGatherSkolemBounds)options.reporter();
			
			Set<Object> atomsBeforeMinimization = new LinkedHashSet<Object>();
			Set<Object> atomsAfterMinimization = new LinkedHashSet<Object>();
			
			//Computing the difference set:
			for(int i = 0; i < translation.numPrimaryVariables(); i++){
				//getting the translation for this proposition: 
				Entry<Relation, TupleSet> trans = MinTwoWayTranslator.translateProposition(translation, reporter.skolemBounds, mapVarToRelation, i+1);

				if(modelBeforeMinimization[i] > 0) //a fact is true before minimization, so store its atoms in the first set.
					atomsBeforeMinimization.addAll(getAtoms(trans.getValue()));
				
				if(modelAfterMinimization[i] > 0) //a fact is true after minimization, so store its atoms in the second set.
					atomsAfterMinimization.addAll(getAtoms(trans.getValue()));
				
				if(modelBeforeMinimization[i] > 0 && modelAfterMinimization[i] < 0){ //if a fact is true before minimization but not after 
					if(trans.getKey().arity() == 1) reducedAttributes++; //The corresponding relation is unary.
					else if(trans.getKey().arity() > 1) reducedRelations++; //The corresponding relation is binary or higher.					
				}
			}
			
			for(Object atom: atomsBeforeMinimization)
				if(!atomsAfterMinimization.contains(atom)) reducedElements++;
			
			reporter.setReducedElements(reducedElements);
			reporter.setReducedAttributes(reducedAttributes);
			reporter.setReducedRelations(reducedRelations);			
		}
		
		/**
		 * Computes all the CFs for the current model loaded in the solver.
		 * @return
		 * @throws TimeoutException
		 * @throws ContradictionException
		 */
		public int[] getConsistentFacts() throws TimeoutException, ContradictionException
		{			
			assert(!trivial);
			
			MinSATSolver solver = (MinSATSolver)translation.cnf();								
			Set<Integer> wantToAdd = new HashSet<Integer>();
			Set<Integer> retVal = new HashSet<Integer>();
			Set<Integer> preservedFacts = new HashSet<Integer>();						
						
			//TODO claimSATSolver does not have to fill all the clauses in here.
			claimSATSolver();
			removeAllConstraints();								
			
			
			// Always deactivate SBP before searching for augmentations
			solver.deactivateSBP();			
			
			// preservedFacts are the positive literals that define the "cone" we are in.
			// wantToAdd are the negative (turned positive) literals we want to check for in the cone.

			int numPrimaryVariables = translation.numPrimaryVariables();
			
			// Do not reference lastSolution here. lastSolution will hold an unsatisfiable
			// Solution result if the iterator is empty. Instead, keep the last instance found:					
			int[] lastPropositionalModelReturned = lastSatSolutionFound.getPropositionalModel();
			
			
			for(int i = 1; i <= numPrimaryVariables; i++){
				if(lastPropositionalModelReturned[i - 1] > 0)
					preservedFacts.add(i);
				else
					wantToAdd.add(i);
			}					
			
			boolean wasSatisfiable = false;
			List<Integer> unitClauses = new ArrayList<Integer>(preservedFacts);
								
			//JOptionPane.showMessageDialog(null, wantToAdd+"\n"+preservedFacts);
			
			// Loop while (a) there are facts left to find and (b) still satisfiable.
			do
			{
				// Add a disjunction for the current set of literals we want to find:
				IConstr removeWTA = null;
				//System.out.println("Adding WTA: "+wantToAdd);
				if(wantToAdd.size() > 1)
				{
					removeWTA = solver.addConstraint(toIntCollection(wantToAdd));
				}
				else
				{
					for(Integer onlyOne : wantToAdd)
						unitClauses.add(onlyOne);
				}
				
				wasSatisfiable = solver.solve(toIntCollection(unitClauses));		
				
				//JOptionPane.showMessageDialog(null, "sat="+wasSatisfiable+"; unitClauses="+unitClauses);

				
				if(wasSatisfiable)
				{
					
					//System.out.println("Model found was: "+Arrays.toString(tempModel));
					Set<Integer> foundAugments = new HashSet<Integer>(); // avoid concurrentmodificationexception
					for(Integer toAdd : wantToAdd)
					{
						// The -1 is because the model is an array (start = 0) 
						// yet our variables start=1
						if(solver.valueOf(toAdd))
						{
							foundAugments.add(toAdd);
							retVal.add(toAdd);
						}
					}

					wantToAdd.removeAll(foundAugments);
				}	
				
				// Remove the targets for this iteration (needed to keep the shared solver clean)
				if(removeWTA != null)
					solver.removeConstraint(removeWTA);
				
			}
			while(wantToAdd.size() > 0 && wasSatisfiable);
			
			// If this is an un-augmented iterator, re-activate symmetry-breaking
			// (Or else the next models would not benefit from SB.)
			if(!isAugmented())
				solver.activateSBP();												
			
			return toIntCollection(retVal);
		}
		
		/**
		 * Returns the translation for this iterator.
		 * @return the translation.
		 */
		public MinTranslation getTranslation(){
			return translation;
		}
		
		/**
		 * Returns the last solution of the iterator.
		 * @return the last solution.
		 */
		private MinSolution getLastSolution(){
			return lastSolution;
		}
		
		/**
		 * Always use this function to update lastSolution.
		 * Otherwise the last prop. model will not be saved.
		 */
		private void setLastSolution(MinSolution last) {
			if(last != null)
				this.lastSolution = last;
			
			if(last.instance() != null)
			{
				this.lastSatSolutionFound = last;
			}			
		}
		
		/**
		 * Returns true if the iterator is an augmentation and returns false otherwise.
		 */
		private boolean isAugmented(){
			return augments != null && augments.length > 0;
		}
		
		//Helpers:
		/**
		 * Considers all the constraints.
		 * @throws ContradictionException
		 */
		private void addAllClauses() throws ContradictionException
		{
			for(Set<Integer> aClause: coneRestrictionClauses)
			{
				coneRestrictionConstraints.add(((MinSATSolver)translation.cnf()).addConstraint(toIntCollection(aClause)));					
			}
		}
		
		/**
		 * Removes all the cone restriction constraints of this iterator.
		 */
		private void removeAllConstraints(){
			Iterator<IConstr> it = coneRestrictionConstraints.iterator();
			while(it.hasNext()){
				IConstr temp = it.next();
				translation.cnf().removeConstraint(temp);
				it.remove();
			}
		}		
		
		private static int[] toIntCollection(Collection<Integer> integers)
		{
		    int[] ret = new int[integers.size()];
		    int iIndex = 0;
		    for(Integer anInt : integers)
		    {
		        ret[iIndex] = anInt;
		    	iIndex++;	    	
		    }
		    return ret;
		}
		
		/**
		 * Converts a list of integers to an ArrayList.
		 * @param list the list.
		 * @return the ArrayList containing the elements of list.
		 */
		private static Set<Integer> toSet(int[] list){
			Set<Integer> retVal = new HashSet<Integer>();
			if(list != null){
				for(int i = 0; i < list.length; i++){
					retVal.add(list[i]);
				}
			}
			
			return retVal;
		}
		
		/**
		 * Returns all the atoms in a TupleSet
		 * @param tuples the input TupleSet
		 * @return a set of atoms
		 */
		private static Set<Object> getAtoms(TupleSet tuples){
			Set<Object> atoms = new HashSet<Object>();
			
			for(Tuple tuple: tuples){
				for(int i = 0; i < tuple.arity(); i++) { atoms.add(tuple.atom(i)); }
			}
			
			return atoms;
		}
	}
	
	/**
	 * Handles the translation of propositional elements to relational facts and vice versa.
	 * Caution: Pass the skolem bounds here.
	 * @author Salman
	 *
	 */
	public static class MinTwoWayTranslator{
		private static Map<Integer, Relation> buildVarToRelationMap(
				MinTranslation translation, Bounds aBounds){
			Map<Integer, Relation> mapVarToRelation = new HashMap<Integer, Relation>(); 
			for(Relation r : aBounds.relations())
			{
				IntSet varsForThisRelation = translation.primaryVariables(r);
				
				//if there is no primary variable for this relation, continue:
				if(varsForThisRelation == null)
					continue;
				
				IntIterator itVarsForThis = varsForThisRelation.iterator();
				while(itVarsForThis.hasNext())
				{
					mapVarToRelation.put(itVarsForThis.next(), r);
				}
					
			}
			
			return mapVarToRelation;
		}
		
		/**
		 * Used for debugging purposes. Print the bijection between propositional
		 * variables and relational facts as a string.
		 * @param translation
		 * @param aBounds
		 * @param mapVarToRelation
		 * @return
		 */
		@SuppressWarnings("unused")
		private static String printTranslation(MinTranslation translation, Bounds aBounds,
				Map<Integer, Relation> mapVarToRelation)
		{
			String outs="";
			
			// Now that we have the mapping from var --> its relation, we can find the tuple:		
			for(int theVar = 1; theVar <= translation.numPrimaryVariables(); theVar++)
			{					
				Relation myRelation = mapVarToRelation.get(theVar);
				
				IntSet s = translation.primaryVariables(myRelation);
				
				Tuple myTuple = getTupleForPropVariable(
							aBounds, translation, s, myRelation, theVar);
									
				outs += (theVar+": "+myTuple+" "+myRelation+" | ");
				if(theVar % 4 == 0)
					outs += "\n";
			}
			
			return outs;				
		}

		
		/**
		 * Converts a set of primary propositional variables into set of relational expressions.
		 * @param translation the translation.
		 * @param aBounds the bounds.
		 * @param mapVarToRelation a map that maps the propositional variables to the relations that they appear in.
		 * @param theVars a VectInt of the variables to convert.
		 * @return
		 */
		private static Instance translatePropositions(MinTranslation translation, Bounds aBounds,
				Map<Integer, Relation> mapVarToRelation, int[] theVars)
		{
			// Populate an empty instance over the universe we're using:
			Instance result = new Instance(aBounds.universe());

			for(int i = 0; i < theVars.length; i++)
			{	
				Entry<Relation, TupleSet> entry = translateProposition(translation, aBounds, mapVarToRelation, theVars[i]);
				Relation myRelation = entry.getKey();
				TupleSet theContents = entry.getValue();
				
				TupleSet currentContents = result.tuples(myRelation);
				if(currentContents != null) // returns null instead of empty set!!
					theContents.addAll(currentContents); 				

				result.add(myRelation, theContents);
			}
			
			// Set<RelationalFact> would be better than Instance. But for now use Instance
			
			// Return an instance (should not be interpreted as a model of the qry!!) that contains
			// only those relational facts indicated by theVars
			return result;				
		}

		/**
		 * Converts a single primary propositional variable to a relational expression.
		 * @param translation the translation.
		 * @param bounds the bounds.
		 * @param mapVarToRelation a map that maps the propositional variables to the relations that they appear in.
		 * @param vars a propositional variable to convert.
		 * @return a Map.Entry object mapping a Relation to a TupleSet.
		 */
		private static Entry<Relation, TupleSet> translateProposition(MinTranslation translation, Bounds bounds, 
				Map<Integer, Relation> mapVarToRelation, final int var){
			Relation myRelation = mapVarToRelation.get(var);

			IntSet s = translation.primaryVariables(myRelation);
			
			Tuple myTuple = getTupleForPropVariable(
						bounds, translation, s, myRelation, var);
				
			// .add here is actually .set -- it overwrites what is already in the relation.
			// So we CANNOT just do:			
			//result.add(myRelation, bounds.universe().factory().setOf(myTuple));
			TupleSet theContents = bounds.universe().factory().setOf(myTuple);
			
			return new SimpleEntry<Relation, TupleSet>(myRelation, theContents);
		}
		
		private static Tuple getTupleForPropVariable(Bounds aBounds, MinTranslation theTranslation, IntSet s, Relation r, int theVar)
		//throws MInternalNoBoundsException
		{
			// The relation's upper bound has a list of tuple indices. The "index" variable below is an index
			// into that list of indices. (If our upper bound was _everything_, would be no need to de-reference.)
	        int minVarForR = s.min();
			
			// Compute index: (variable - minvariable) of this relation's variables 
	        int index = theVar - minVarForR;
	        
	        // OPT: How slow is this? May want to cache...
	        int[] arr = aBounds.upperBound(r).indexView().toArray();
	        
	        TupleFactory factory = aBounds.universe().factory();   
	        Tuple tup = factory.tuple(r.arity(), arr[index]);  

	        //MCommunicator.writeToLog("\ngetTupleForPropVariable: thisTuple="+tup+" for "+theVar+". Relation had vars: "+s+" and the offset was "+minVarForR+
	        //		"leaving index="+index+". Upper bound indexview: "+Arrays.toString(arr)+
	        //		"\nThe de-referenced tuple index is: "+arr[index]);

	        return tup;
		}
		
		private static int getPropVariableForTuple(Bounds aBounds, MinTranslation translation, Relation r, Tuple tuple){
			IntSet s = translation.primaryVariables(r);

			//if there is no primary variable for this relation, return -1
			if(s == null)
				return -1;
			
			TupleSet upperBound = aBounds.upperBound(r);
			
			if(upperBound == null)
				return -1;
			
			int[] arr = upperBound.indexView().toArray();

			
	        TupleFactory factory = aBounds.universe().factory();
	        
	        int index = -1;
	        //Not the best way of doing this!
	        for(int i = 0; i < arr.length; i++){
	        	if(tuple.equals(factory.tuple(r.arity(), arr[i])))
	        		index = i;
	        }
	        
	        if(index == -1)
	        	return -1;
	        
			return s.min() + index;//s.min() + tuple.index();
		}
	}
	
}
