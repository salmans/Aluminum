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

import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Set;

import javax.swing.JOptionPane;

import kodkod.engine.satlab.SATSolver;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 * Implementor of Kodkod's SATSolver interface. Used as a wrapper atop SAT4J, 
 * but more importantly this class allows the caller to activate and deactivate
 * all symmetry-breaking clauses. Also stores the last propositional model seen
 * for use by consistent-fact generation. 
 */
public final class MinSATSolver implements SATSolver {
	private ISolver solver;
	private final ReadOnlyIVecInt wrapper;
	private Boolean sat; 
	private int vars, clauses;
	private int[] lastModel = null;
	
	// If toRemoveSBP is empty,
	boolean sbpActive = true;
	private Set<int[]> sbpClauses = new HashSet<int[]>();
	private Set<IConstr> toRemoveSBP = new HashSet<IConstr>();
	private Set<Integer> sbpUnitClauses = new HashSet<Integer>();
	
	public int internalNumConstraints()
	{
		return solver.nConstraints();
	}
	
	void clc()
	{
		solver.clearLearntClauses();
	}
	
	/**
	 * Returns the number of clauses in the SBP, including unit clauses.
	 * @return
	 */
	public int numSBPClauses()
	{
		return sbpClauses.size() + sbpUnitClauses.size();
	}
	
	/**
	 * Returns whether or not the SBP is included in the solver.
	 * Calls to activateSBP and deactiveSBP will flip this value.
	 * @return
	 */
	public boolean sbpActive()
	{
		return sbpActive;
	}
		
	/**
	 * Call to augment the solver's clause set with the SBP clauses.
	 * No effect (returns false) if SBP is already included.
	 * @return
	 */
	public boolean activateSBP() 
	{		
		if(sbpActive) return false;
				
		for(int[] lits : sbpClauses)
		{
			try {
				// Unit clauses should have been moved to sbpUnitClauses already,
				// so safe to do this without checking for UnitClause
				IConstr toRemove = solver.addClause(wrapper.wrap(lits));
				//JOptionPane.showMessageDialog(null, toRemove);
				if(toRemove != null) 
				{					
					toRemoveSBP.add(toRemove);
				}
			} catch (ContradictionException e) {				
				sat = Boolean.FALSE;		
				JOptionPane.showMessageDialog(null, "CONTRADICTION EXCEPTION in activateSBP");
			}
		}
		
		//JOptionPane.showMessageDialog(null, "asbp:"+solver.nConstraints());
		sbpActive = true;	
		return true;
	}
	
	/**
	 * Call to *remove* SBP clauses from the solver.
	 * No effect (returns false) if SBP is not included already.
	 * @return
	 */
	public boolean deactivateSBP()
	{
		if(!sbpActive) return false;
		
		// The current implementation of sat4j does not handle REMOVING unit clauses; it forces
		// the use of assumptions. So we need the separate assumptions list above.
		for(IConstr toRemove : toRemoveSBP)
		{					
			// Expect no UnitClauses here
			solver.removeConstr(toRemove);
		}
		
		// s/b same size
		//JOptionPane.showMessageDialog(null, "dsbp:"+(foo-solver.nConstraints())+"; "+toRemoveSBP.size());
		
		toRemoveSBP.clear();
		sbpActive = false;
		return true;
	}
	
	/** Fills lastModel from solver.model(). We have to do this because sometimes,
	 * the solver drops some indices.
	 */
	public void setLastModel() {
		int[] model = solver.model();
		lastModel = new int[vars];

		//in the minimization algorithm, we want to treat unknown variables 
		//(don't cares) as they are true.		
		for(int i = 1; i <= vars; i++){
			lastModel[i - 1] = i; 
		}
		
		for(int i = 0; i < model.length; i++){
			int value = model[i];
			
			if(value < 0)
				lastModel[-value - 1] = value;
		}
	}	
	
	public int[] getLastModel() {
		return lastModel;
	}

	/**
	 * Constructs a wrapper for the given instance
	 * of ISolver.
	 * @throws NullPointerException - solver = null
	 */
	MinSATSolver(ISolver solver) {
		if (solver==null)
			throw new NullPointerException("solver");
		this.solver = solver;
		this.wrapper = new ReadOnlyIVecInt();
		this.sat = null;
		this.vars = this.clauses = 0;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public int numberOfVariables() {
		return vars; 
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public int numberOfClauses() {
		return clauses; 
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 */
	public void addVariables(int numVars) {
		if (numVars < 0)
			throw new IllegalArgumentException("numVars < 0: " + numVars);
		else if (numVars > 0) {
			vars += numVars;
			solver.newVar(vars);
		}
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#addClause(int[])
	 */
	public boolean addClause(int[] lits) {
		//System.out.println("(nonsb) CLAUSE ADDED: "+Arrays.toString(lits));
		try {
			//if (!Boolean.FALSE.equals(sat)) {
				clauses++;
				solver.addClause(wrapper.wrap(lits));
				//JOptionPane.showMessageDialog(null,Arrays.toString(lits));
//				for(int lit : lits) {
//					System.out.print(lit + " ");
//				}
//				System.out.println(0);
				return true;
			//}
			
		} catch (ContradictionException e) {
			sat = Boolean.FALSE;
			JOptionPane.showMessageDialog(null, "CONTRADICTION EXCEPTION in addClause");
		}
		return false;
	}
	
	static boolean isTautology(int[] lits)
	{			
		Set<Integer> litsSet = new HashSet<Integer>(lits.length);
		for(int ii : lits)
			litsSet.add(ii);
		for(Integer ii : litsSet)
			if(litsSet.contains(-ii))
				return true;
		return false;
	}
	
	public boolean addSBPClause(int[] lits)
	{
		//System.out.println("SBP CLAUSE ADDED: "+Arrays.toString(lits));
		// Can't just call addClause, that would obstruct the IConstr
		try {			

			// Still need to use assumptions...
			if(lits.length <= 1)
			{
				sbpUnitClauses.add(lits[0]);
			}
			else
			{
				// Don't try to add a clause we already have. 
				// TODO: This is order-dependent (since passed as array). 
				// Caller needs to make sure there are no identical (up to ordering) clauses...
				if(sbpClauses.contains(lits))					
					return true;
				
				IConstr toRemove = solver.addClause(wrapper.wrap(lits));
			
				// DO NOT store wrapper.wrap(lits); it's in a read only field that is re-used. 
				sbpClauses.add(lits.clone());
			
				if(toRemove != null)
				{
					//JOptionPane.showMessageDialog(null, "toRemove="+toRemove);
					toRemoveSBP.add(toRemove);
				}			
			}
						
			return true;			
		} catch (ContradictionException e) {
			sat = Boolean.FALSE;
			JOptionPane.showMessageDialog(null, "CONTRADICTION EXCEPTION in addSBPClause");
		}
		return false;
	}
	
	/**
	 * Similar to addClaue but returns the constraint.
	 * @param lits the literals
	 * @return the constraint
	 * @throws ContradictionException
	 */
	public IConstr addConstraint(int[] lits) throws ContradictionException {
		clauses++;
		IConstr temp = solver.addClause(wrapper.wrap(lits));
		return temp;
	}	
	
	/**
	 * Removes a constraint from the underlying SATSolver.
	 * @param constraint the constraint
	 * @return the value from solver.removeConstr(arg0)
	 */
	public boolean removeConstraint(IConstr constraint){
		clauses--;
		return solver.removeConstr(constraint);
	}
	
	/**
	 * Returns the assumptions given plus SBP assumptions if SBP is active
	 * @param assumptions
	 * @return
	 */
	IVecInt getAssumptions(int[] assumptions)
	{
		//System.out.println("Getting assumptions. SBP="+sbpActive);
		if(sbpActive)
		{
			int[] together = new int[assumptions.length+sbpUnitClauses.size()];
			for(int ii=0;ii<assumptions.length;ii++)
				together[ii] = assumptions[ii];
			int ii = 0;
			for(Integer unit : sbpUnitClauses)
			{
				together[ii+assumptions.length] = unit;
				ii++;
			}
							
			//JOptionPane.showMessageDialog(null, "assumptions (+sbp):"+Arrays.toString(together));
			
			return new VecInt(together);
		}
		else
		{
			//JOptionPane.showMessageDialog(null, "assumptions (-sbp):"+Arrays.toString(assumptions));
			return new VecInt(assumptions);
		}
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */
	public boolean solve(boolean saveModel) {
		try {
			//if (!Boolean.FALSE.equals(sat)){
				sat = Boolean.valueOf(solver.isSatisfiable(getAssumptions(new int[] {})));
				if(sat && saveModel)
					setLastModel();
				
				
			//}
			return sat;
		} catch (org.sat4j.specs.TimeoutException e) {
			throw new RuntimeException("timed out");
		} 
	}
	
	public boolean solve()
	{
		return solve(true);
	}
	public boolean solve(int[] assumptions)
	{
		return solve(assumptions, true);
	}
	
	/**
	 * {@inheritDoc}
	 * @param assumptions additional assumptions for the SATSolver
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */
	public boolean solve(int[] assumptions, boolean saveModel) {
		try {			
			sat = Boolean.valueOf(solver.isSatisfiable(getAssumptions(assumptions)));
				
			/*org.sat4j.minisat.core.Solver aSolver = (org.sat4j.minisat.core.Solver) solver;
			String s = "";
			for(int ii=0;ii<aSolver.nConstraints();ii++)
				s+= aSolver.getIthConstr(ii)+", "+((ii%5 ==0)?"\n":"");
			//JOptionPane.showInputDialog("",s);
			JOptionPane.showMessageDialog(null,s);
			*/
			
		/*	ISolver sol2 = SolverFactory.instance().defaultSolver();
			sol2.reset();
			sol2.newVar(vars);
			String s = "; vars="+vars+": \n";
			try {
				for(int[] lits : sbpClauses)
				{
					s += Arrays.toString(lits)+" ";
					sol2.addClause(new VecInt(lits));					
				}
					
				//for(int lit : sbpUnitClauses)
				//{
				//	s += lit+" ";	
				//	sol2.addClause(new VecInt(lit));					
				//}
								
			} catch (ContradictionException e) {
				
				JOptionPane.showMessageDialog(null,"CONTRADICTION!");
			}
			
			List<Integer> tempunits = new ArrayList<Integer>(sbpUnitClauses);
			tempunits.add(1);
			tempunits.add(-2);
			
			//JOptionPane.showMessageDialog(null, sol2.isSatisfiable(new VecInt(new int[] {1, -2}))+s); // true ???
			JOptionPane.showMessageDialog(null, sol2.isSatisfiable(new VecInt(MinSolver.MinSolutionIterator.toIntCollection(tempunits)))+s); // true ???
			
			org.sat4j.minisat.core.Solver aSolver = (org.sat4j.minisat.core.Solver) sol2;
			
			for(int ii=0;ii<aSolver.nConstraints();ii++)
				s+= aSolver.getIthConstr(ii)+", "+((ii%5 ==0)?"\n":"");
			//JOptionPane.showInputDialog("",s);
			JOptionPane.showMessageDialog(null,s);
			*/
			
			/*s ="SB clauses: ";
			for(int[] lits : sbpClauses)
			{
				s += Arrays.toString(lits)+" ";				
			}
			s +="\n";
			for(int lit : sbpUnitClauses)
			{
				s += lit + " ";				
			}
			JOptionPane.showMessageDialog(null,s);
			*/
			
			if(sat && saveModel)
				setLastModel();			
			return sat;
			
		} catch (org.sat4j.specs.TimeoutException e) {
			throw new RuntimeException("timed out");
		} 
	}	

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	/*public final boolean valueOf(int variable) {
		if (!Boolean.TRUE.equals(sat)) 
			throw new IllegalStateException();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars+"]");
		return solver.model(variable);
	}*/

	/**
	 * Returns the value of a variable in the last retrieved model.
	 * @param variable the variable
	 * @return boolean value of the variable in the last retrieved  model.
	 */
	public final boolean valueOf(int variable) {
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars+"]");
		
		return (lastModel[variable - 1] > 0) ? true: false;
	}	
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#free()
	 */
	public synchronized final void free() {
		//solver = null;
	}
	
	/**
	 * A wrapper for an int array that provides
	 * read-only access to the array via the IVecInt interface. 
	 * 
	 * @author Emina Torlak
	 */
	private static final class ReadOnlyIVecInt implements IVecInt {
		private static final long serialVersionUID = 1L;
		private int[] vec;
		
		/**
		 * Sets this.vec to the given vector
		 * and returns this.
		 */
		IVecInt wrap(int[] vec) {
			this.vec = vec;
			return this;
		}
		
		public int size() {
			return vec.length;
		}

		public boolean isEmpty() {
			return size() == 0;
	    }
		
		public void shrink(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void shrinkTo(int arg0) {
			throw new UnsupportedOperationException();
		}

		public IVecInt pop() {
			throw new UnsupportedOperationException();
		}

		public void growTo(int arg0, int arg1) {
			throw new UnsupportedOperationException();
		}

		public void ensure(int arg0) {
			throw new UnsupportedOperationException();
		}

		public IVecInt push(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void unsafePush(int arg0) {
			throw new UnsupportedOperationException();
		}

		public int unsafeGet(int arg0) {
			return vec[arg0];
		}

		public void clear() {
			throw new UnsupportedOperationException();
		}

		public int last() {
			return vec[vec.length - 1];
		}

		public int get(int arg0) {
			if (arg0 < 0 || arg0 >= vec.length)
				throw new IndexOutOfBoundsException("arg0: " + arg0);
			return vec[arg0];
		}

		public void set(int arg0, int arg1) {
			throw new UnsupportedOperationException();		
		}

		public boolean contains(int arg0) {
			for(int i : vec) {
				if (i==arg0) return true;
			}
			return false;
		}

		public void copyTo(IVecInt arg0) {
			int argLength = arg0.size();
			arg0.ensure(argLength + vec.length);
			for(int i : vec) {
				arg0.set(argLength++, i);
			}
		}

		public void copyTo(int[] arg0) {
			assert arg0.length >= vec.length;
			System.arraycopy(vec,0, arg0, 0, vec.length);
		}

		public void moveTo(IVecInt arg0) {
			throw new UnsupportedOperationException();	
		}

		public void moveTo2(IVecInt arg0) {
			throw new UnsupportedOperationException();	
		}

		public void moveTo(int[] arg0) {
			throw new UnsupportedOperationException();	
		}

		public void moveTo(int arg0, int arg1) {
			throw new UnsupportedOperationException();	
		}

		public void insertFirst(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void remove(int arg0) {
			throw new UnsupportedOperationException();
		}

		public int delete(int arg0) {
			throw new UnsupportedOperationException();
		}

		public void sort() {
			throw new UnsupportedOperationException();
		}

		public void sortUnique() {
			throw new UnsupportedOperationException();
		}

		public IteratorInt iterator() {
			return new IteratorInt() {
				int cursor = 0;
				public boolean hasNext() {
					return cursor < vec.length;
				}
				public int next() {
					if (!hasNext()) 
						throw new NoSuchElementException();
					return vec[cursor++];
				}
			};
		}

		public int containsAt(int e) {
			for(int n=vec.length, i=0; i<n; i++) if (vec[i]==e) return i;
			return -1;
		}

		public int containsAt(int e, int from) {
			if (from<vec.length) for(int n=vec.length, i=from+1; i<n; i++) if (vec[i]==e) return i;
			return -1;
		}
		
		@Override
		public int[] toArray() {
			throw new UnsupportedOperationException();
		}

		@Override
		public int indexOf(int arg0) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void moveTo(int arg0, int[] arg1) {
			throw new UnsupportedOperationException();
			
		}

		@Override
		public IVecInt[] subset(int arg0) {
			throw new UnsupportedOperationException();
		}		
	}	
	
	public String printConstraints()
	{
		// For debug: print out the clauses...
		@SuppressWarnings("rawtypes")
		org.sat4j.minisat.core.Solver aSolver = (org.sat4j.minisat.core.Solver) this.solver;
		
		String s = "";
		for(int ii=0;ii<aSolver.nConstraints();ii++)
			s += aSolver.getIthConstr(ii)+",    "+((ii%4 ==0)?"\n":"");
		return s;
	}
}
