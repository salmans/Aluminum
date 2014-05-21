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
package minkodkod.engine.fol2sat;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import minkodkod.MinSATSolver;

import kodkod.ast.Relation;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.bool.BooleanValue;
import kodkod.engine.bool.BooleanVariable;
import kodkod.engine.bool.BooleanVisitor;
import kodkod.engine.bool.ITEGate;
import kodkod.engine.bool.MultiGate;
import kodkod.engine.bool.NotGate;
import kodkod.engine.bool.Operator.Nary;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

// ALUMINUM: Separates solving and translation time; keeps symmetries detected for use in cone clauses 

/**
 * Stores the translation of a {@link kodkod.ast.Formula kodkod formula}
 * to CNF. 
 * 
 * @specfield formula: Formula // the formula that was translated
 * @specfield bounds: Bounds // the bounds used to obtain the CNF from the formula 
 * @specfield solver: SATSolver // a SATSolver containing the CNF representation of the formula
 * @specfield options: Options // the options object used to control translation parameters
 * @author Emina Torlak
 */
public final class MinTranslation {
	private final Bounds bounds;
	private final MinSATSolver solver;
	/* maps relations to the literals that comprise their translations */
	private final Map<Relation, IntSet> primaryVarUsage;
	private final TranslationLog log;
	private final int maxPrimaryLit;
	
	public final Set<IntSet> symmetries;
	//public final Set<Map<Integer, Integer>> permutations;
	public final List<Map<Integer, Integer>> permutations;
	public final BooleanValue sbpValue;
	
	/**
	 * Constructs a new Translation object for the given solver, bounds,  mapping
	 * from Relations to literals, and TranslationLog.
	 * @requires maxPrimaryLit = max(varUsage[Relation].max)
	 * @requires bounds.relations = varUsage.IntSet
	 * @effects this.solver' = solver && this.bounds' = bounds
	 */
	MinTranslation(MinSATSolver solver, Bounds bounds, Map<Relation, IntSet> varUsage,
			int maxPrimaryLit, TranslationLog log, Set<IntSet> symmetries,
			List<Map<Integer, Integer>> permutations,
			BooleanValue sbpValue) {			
		this.solver = solver;				
		this.bounds = bounds;
		this.primaryVarUsage = varUsage;
		this.maxPrimaryLit = maxPrimaryLit;
		this.log = log;
		this.symmetries = symmetries;		
		this.permutations = permutations;
		this.sbpValue = sbpValue;
	}

	/**
	 * Returns a SATSolver object initialized with the CNF encoding of this.formula 
	 * and the timeout and random seed values specified by this.options.  Satisfiability
	 * of the formula can be checked by calling {@link kodkod.engine.satlab.SATSolver#solve()}.
	 * @return {s: SATSolver | [[s.clauses]] = [[this.formula]] && s.timeout() = this.options.timeout() && 
	 *                         s.seed() = this.options.seed() } 
	 */
	public MinSATSolver cnf() {
		return solver;
	}
	
	/**
	 * If this.solver.solve() is true, returns 
	 * an interpretation of the cnf solution as a 
	 * mapping from Relations to sets of Tuples.  The Relations
	 * mapped by the returned instance are either leaves
	 * of this.formula with different lower and upper
	 * bounds (i.e. {r: this.formula.*children & Relation | 
	 * this.bounds.upperBound[r] != this.bounds.lowerBound[r]}), 
	 * or skolem constants.
	 * @return an interpretation of the cnf solution as
	 * a mapping from (this.variableUsage().keySet() & Relation) to sets of Tuples.
	 * @throws IllegalStateException - this.solver.solve() has not been called or the 
	 * outcome of the last call was not <code>true</code>.
	 */
	public Instance interpret() {
		final TupleFactory f = bounds.universe().factory();
		final Instance instance = new Instance(bounds.universe());
//		System.out.println(varUsage);
		for(Relation r : bounds.relations()) {
			TupleSet lower = bounds.lowerBound(r);
			IntSet indeces = Ints.bestSet(lower.capacity());
			indeces.addAll(lower.indexView());
			IntSet vars = primaryVarUsage.get(r);
			if (vars!=null) {
				int lit = vars.min();
				for(IntIterator iter = bounds.upperBound(r).indexView().iterator(); iter.hasNext();) {
					final int index = iter.next();
					if (!indeces.contains(index) && solver.valueOf(lit++))
						indeces.add(index);
				}
			}
			instance.add(r, f.setOf(r.arity(), indeces));
		}
		return instance;
	}
	
	/**
	 * Returns the set of primary variable literals  that represent
	 * the tuples in the given relation.  If no literals were allocated
	 * to the given relation, null is returned.
	 * @return the set of primary variable literals that represent
	 * the tuples in the given relation. 
	 */
	public IntSet primaryVariables(Relation relation) {
		return primaryVarUsage.get(relation);
	}
	
	/**
	 * Returns the number of primary variables allocated 
	 * during translation.  Primary variables represent
	 * the tuples of Relations that are either leaves
	 * of this.formula with different lower and upper
	 * bounds (i.e. {r: this.formula.*children & Relation | 
	 * this.bounds.upperBound[r] != this.bounds.lowerBound[r]}), 
	 * or skolem constants.
	 * @return the number of primary variables allocated
	 * during translation.
	 */
	public int numPrimaryVariables() {
		return maxPrimaryLit;
	}
	
	/**
	 * If this.options.logTranslation was set to true, returns the log of the
	 * translation that produced this Translation object.  Otherwise returns null.
	 * @return the log of the translation that produced this Translation
	 * object, if this.options.logTranslation was enabled during translation, or null if not. 
	 */
	public TranslationLog log() {
		return log;
	}
	
	// IMPORTANT: This function can't just check every SBP clause. Minimal models are produced with SBP *OFF*
	// and so any secondary variables in the SBP clauses may not match. We need instead to evaluate the original
	// SBP Boolean circuit on this model.
	public boolean satisfiesSBP(int[] propositionalModel) {
		Set<Integer> positives = new HashSet<Integer>(propositionalModel.length);
		
		for(int x : propositionalModel) {
			if(x > 0) positives.add(x);		
		}
				
		if(sbpValue instanceof BooleanFormula)
			return ((BooleanFormula)sbpValue).accept(new BooleanFormulaEvaluator(positives), 0);
		else
			return true;		
	}
	
	// TODO: share code between this and satisfiesSBP.
	public boolean negationSatisfiesSBP(Set<Integer> negatedModel) {
		Set<Integer> positives = new HashSet<Integer>(negatedModel.size());
		
		for(int x : negatedModel) {
			if(x < 0) positives.add(-1*x);		
		}
						
		if(sbpValue instanceof BooleanFormula)
			return ((BooleanFormula)sbpValue).accept(new BooleanFormulaEvaluator(positives), 0);
		else
			return true;		
	}
	
}

// Can't trust secondary variables at all. So need to restrict the input to only primary literals

final class BooleanFormulaEvaluator implements BooleanVisitor<Boolean, Integer> {
	final Set<Integer> positives;
	
	public BooleanFormulaEvaluator(Set<Integer> positives) {
		this.positives = positives;
	}
	
	private boolean andHelper(MultiGate multigate, int depth)
	{
		for(int ii=0;ii<multigate.size();ii++) {
			if(! multigate.input(ii).accept(this, depth+1))
				return false;			
		}		
		return true;	
	}

	private boolean orHelper(MultiGate multigate, int depth)
	{
		for(int ii=0;ii<multigate.size();ii++) {
			if(multigate.input(ii).accept(this, depth+1))
				return true;
		}
		return false;
	}
	
	private String pad(int depth) 
	{
		 return new String(new char[depth]).replace("\0", "  ");
	}
	
	@Override
	public Boolean visit(MultiGate multigate, Integer depth) {		
		boolean result;
		
		//System.out.println(pad(depth)+"checking "+multigate+": ");		

		if(multigate.op() == Nary.AND) {
			result = andHelper(multigate, depth);
					
		} else if(multigate.op() == Nary.OR) { 
			result = orHelper(multigate, depth);
		}
		else { 
			throw new UnsupportedOperationException("BooleanFormulaEvaluator encountered op = "+multigate.op());
		}
		
		//System.out.println(pad(depth)+"result: "+result);
		return result;		
	}

	@Override
	public Boolean visit(ITEGate ite, Integer depth) {
		// 0 ? 1 : 2
		boolean result;
		//System.out.println(pad(depth)+"checking "+ite+": ");
		if(ite.input(0).accept(this,  depth+1)) 
			result = ite.input(1).accept(this, depth+1);
		else 
			result = ite.input(2).accept(this, depth+1);
		
		//System.out.println(pad(depth)+"result: "+result);
		return result;
	}

	@Override
	public Boolean visit(NotGate negation, Integer depth) {
		// not 0 				
		//System.out.println(pad(depth)+"checking "+negation+": ");
		return ! negation.input(0).accept(this, depth+1);		
	}

	@Override
	public Boolean visit(BooleanVariable variable, Integer depth) {
		// v
		//System.out.println(pad(depth)+"checking bool var "+variable+": "+positives.contains(variable.label()));
		return positives.contains(variable.label()); 
	}

}

