import java.util.*;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import MinSolver.*;

import kodkod.ast.*;
import kodkod.ast.visitor.*;
import kodkod.instance.*;
import kodkod.engine.fol2sat.TrivialFormulaException;
import kodkod.engine.satlab.*;

class MIntArrayWrapper
{
    private int hashCode;
    private int[] theArray;
    private int length;
    
    MIntArrayWrapper(int[] theArray)
    {        
    	// Caller is obligated to make a COPY of the clause array passed by Kodkod.
        this.theArray = theArray; 
        hashCode = Arrays.hashCode(theArray);
        this.length = theArray.length;       
    }
    
    public boolean equals(Object obj)
    {
        if(obj instanceof MIntArrayWrapper)
            return Arrays.equals(theArray, ((MIntArrayWrapper)obj).theArray);
        return false;
    }

    public int hashCode()
    {
        return hashCode;
    }
    
    public int size()
    {
        return length;
    }
    
    public int get(int index)
    {
        return theArray[index]; // no out of bounds protection
    }
    
    public int[] getArray()
    {
    	return theArray;
    }
    
    public String toString()
    {
        StringBuffer result = new StringBuffer();
        for(int ii=0;ii<size();ii++)
        {
            result.append(get(ii));
            result.append(" ");
        }
        
        return result.toString();
    }
        
}


class CNFSpy implements SATSolver
{
    List<MIntArrayWrapper> clauses = new ArrayList<MIntArrayWrapper>();
    SATSolver internalSolver;
    SATFactory mySATFactory;
    
    CNFSpy(SATFactory mySATFactory)
    {
        // Spy on Kodkod -- remember the clauses given.
        internalSolver = mySATFactory.instance();
        this.mySATFactory = mySATFactory;
    }    
    
	@Override
    public void free()
    {
        internalSolver.free();
        clauses.clear();
    }

        
    @Override
    public boolean addClause(int[] lits)
    {
        // "No reference to the specified array is kept, so it can be reused."
        //  (From Kodkod Java doc)
        // Kodkod _does_ re-use, so we can't wrap lits directly; we need to copy first.
        
        int[] litsCopy = Arrays.copyOf(lits, lits.length);
        MIntArrayWrapper wrapper = new MIntArrayWrapper(litsCopy);

       // MEnvironment.errorStream.println("ADDED CLAUSE after "+clauses.size()+" others. It was: "+Arrays.toString(litsCopy));
        
        clauses.add(wrapper);
        return internalSolver.addClause(lits);
    }
    
    public void printClauses()
    {
    	int iClause = 0;
    	for(MIntArrayWrapper aClause : clauses)
    	{
    		System.out.println("Clause "+iClause+": "+Arrays.toString(aClause.getArray()));
    		iClause++;    			
    	}
    }

    public ISolver getEquivalentSAT4j()
    throws ContradictionException
    {
    	// Do not have access to the internal ISolver object that Kodkod keeps. But we can re-create.
    	
    	ISolver result = SolverFactory.newDefault();
    	result.newVar(internalSolver.numberOfVariables());
    	// no!
    	//result.setExpectedNumberOfClauses(internalSolver.numberOfClauses());
    	result.setTimeout(36000); // 10 hrs (just in case)
    	
   		for(MIntArrayWrapper aClause : clauses)
   		{
   			// swap if need the IConstr
   			//IConstr x = result.addClause(new VecInt(aClause.getArray()));
   			result.addClause(new VecInt(aClause.getArray()));
			
   			//PrintWriter pw = new PrintWriter(MEnvironment.errorStream);
			//result.printInfos(pw, ":::: ");
			//pw.flush();
   			
			//if(x == null)
   			//MEnvironment.errorStream.println("conv: "+x + " : "+aClause.toString());
   			// sometimes null, but not always
   			// taut, cont, or... unit?
   		}
    	    	
    	return result;
    }
    
    public CNFSpy makeCopy()
    {
    	// Copy this solver.
    	// Yes, that means internalSolver.addClause calls. :(
    	
    	CNFSpy newSolver = new CNFSpy(mySATFactory);
    	newSolver.addVariables(internalSolver.numberOfVariables());
    	// Can't use the same clauses set. But we can use the same arrays (no need to *copy* each clause)
    
    	for(MIntArrayWrapper wrapper : clauses)
    	{
    		newSolver.clauses.add(wrapper);
    		newSolver.internalSolver.addClause(wrapper.getArray());
    		
    		// DEBUG
    		// Is this lovely clause tautologous?
    		// slow for now
    		/*for(int ii=0;ii<wrapper.size();ii++)
    			for(int jj=ii+1;jj<wrapper.size();jj++)
    			{
    				if(Math.abs(wrapper.get(ii)) == Math.abs(wrapper.get(jj)))
    					MEnvironment.errorStream.println("TAUT");
    			}*/
    	}
    	
    	
    	return newSolver;
    }
    
    @Override
    public void addVariables(int numVars) {
        internalSolver.addVariables(numVars);
        
    }

    @Override
    public int numberOfClauses() {
        return internalSolver.numberOfClauses();
    }

    @Override
    public int numberOfVariables() {
        return internalSolver.numberOfVariables();
    }

    @Override
    public boolean solve() throws SATAbortedException
    {
        return internalSolver.solve();
    }

    @Override
    public boolean valueOf(int variable)
    {
        return internalSolver.valueOf(variable);
    }

}

class CNFSpyFactory extends SATFactory
{
    private SATFactory mySATFactory;
    
    CNFSpyFactory(SATFactory mySATFactory)
    {
        this.mySATFactory = mySATFactory;    
    }
    
    @Override
    public SATSolver instance()
    {
        return new CNFSpy(mySATFactory);                      
    }
    
}



class FreeVariableCollectionV extends AbstractCollector<Variable> {
	public HashSet<Variable> newSet() {
		return new HashSet<Variable>();
	}

	public FreeVariableCollectionV() {
		super(new HashSet<Node>());
	}

	public Set<Variable> visit(Variable v) {
		if (cache.containsKey(v))
			return lookup(v);
		cached.add(v);

		HashSet<Variable> tempset = new HashSet<Variable>();
		tempset.add(v);
		return cache(v, tempset);
	}

	public Set<Variable> visit(QuantifiedFormula qf) {
		if (cache.containsKey(qf))
			return lookup(qf);
		cached.add(qf);

		// What free variables appear inside this quantifier?
		// Re-create the set because we may get an immutable singleton back, and we remove from it below.
		Set<Variable> tempset = new HashSet<Variable>(qf.formula().accept(this));

		// These variables are quantified in this scope.
		// (Don't worry about re-quantification later, since Kodkod won't run
		// vs. such a formula.)
		for (Decl d : qf.decls())
		{
			
			tempset.remove(d.variable());
		}

		return cache(qf, tempset);
	}
}

class FormulaStruct{
	Formula fmla;
	Bounds bounds;
	
	public FormulaStruct(Formula fmla, Bounds bounds){
		this.fmla = fmla;
		this.bounds = bounds;
	}

	public Formula getFmla() {
		return fmla;
	}
	public void setFmla(Formula fmla) {
		this.fmla = fmla;
	}
	public Bounds getBounds() {
		return bounds;
	}
	public void setBounds(Bounds bounds) {
		this.bounds = bounds;
	}		
}

public class Main {	
	
	private static FormulaStruct formula0(){
		// TN: very basic fmla
		// Every element is in either r1 or r2, possibly both:
				
		Relation r1 = Relation.unary("R1");
		Relation r2 = Relation.unary("R2");
		
		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
		
		Formula f = Expression.UNIV.in(r1.union(r2));
		Bounds b = new Bounds(u);
		TupleFactory tfac = u.factory();
		b.bound(r1, tfac.noneOf(1), tfac.allOf(1));
		b.bound(r2, tfac.noneOf(1), tfac.allOf(1));
		return new FormulaStruct(f, b);
	}

	
	private static FormulaStruct formula1(){
		Variable x = Variable.unary("x");
		Relation r1 = Relation.unary("R1");
		Relation r2 = Relation.unary("R2"); 
		Relation r3 = Relation.unary("R3");
		
		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
		
		Formula f = x.in(r1).or(x.in(r2)).and(x.in(r3)).forSome(x.oneOf(Expression.UNIV));
		Bounds b = new Bounds(u);
		TupleFactory tfac = u.factory();
		b.bound(r1, tfac.noneOf(1), tfac.allOf(1));
		b.bound(r2, tfac.noneOf(1), tfac.allOf(1));
		b.bound(r3, tfac.noneOf(1), tfac.allOf(1));
				
		return new FormulaStruct(f, b);
	}

	private static FormulaStruct formula2(){
		Variable x = Variable.unary("x");
		Variable y = Variable.unary("y");
		Expression xy = x.product(y);
		Expression yx = y.product(x);
		Formula f = null;

		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
		TupleFactory tfac = u.factory();
		Bounds b = new Bounds(u);
		
		
		for(int i = 0; i < 100; i++){
			Relation r = Relation.binary("R" + i);
			b.bound(r, tfac.noneOf(2), tfac.allOf(2));
			Formula temp = xy.in(r).and(yx.in(r)); 
			if(f == null)
				f = temp;
			else
				f = f.or(temp);
		}
		f = f.forSome(x.oneOf(Expression.UNIV)).forSome(y.oneOf(Expression.UNIV));
		return new FormulaStruct(f, b);
	}

	//Multiplication where variables interleave (This example is not that interesting!).
	private static FormulaStruct formula3(){
		int size = 4;
		Formula f = null;
		Formula temp = null;

		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
		TupleFactory tfac = u.factory();
		Bounds b = new Bounds(u);

		ArrayList<Variable> xs = new ArrayList<Variable>();
		ArrayList<Variable> ys = new ArrayList<Variable>();
		
		for(int i = 0; i < size; i++){
			xs.add(Variable.unary("x" + i));
			ys.add(Variable.unary("y" + i));
		}
	
		Relation r = Relation.unary("R");
		b.bound(r, tfac.noneOf(1), tfac.allOf(1));

		for(int i = 0; i < size * 2; i++){
			int min = (i < size) ? 0: i - size + 1;
			int max = (i < size) ? i: size - 1;
			int offset = i < size? 0: i - size + 1;
			
			temp = null;
			
			for(int j = min; j <= max; j++){
				Formula t = xs.get(j).in(r).and(ys.get(max - j + offset).in(r));
				temp = (temp == null) ? t: temp.or(t);
			}
			
			if(temp != null)
				f = (f == null) ? temp: f.and(temp);
		}
		
		for(int i = 0; i < size; i++){
			f = f.forSome(xs.get(i).oneOf(Expression.UNIV));
			f = f.forSome(ys.get(i).oneOf(Expression.UNIV));
		}

		return new FormulaStruct(f, b);
	}
	
	//Multiplication where relations interleave.
	private static FormulaStruct formula4(){
		int size = 4;
		Formula f = null;
		Formula temp = null;

		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
		TupleFactory tfac = u.factory();
		Bounds b = new Bounds(u);

		Variable x = Variable.unary("x");
		Variable y = Variable.unary("y");
		Expression xy = x.product(y);
	
		
		ArrayList<ArrayList<Relation>> relations = new ArrayList<ArrayList<Relation>>();
		for(int i = 0; i < size; i++){
			ArrayList<Relation> relation = new ArrayList<Relation>();
			relations.add(relation);
			for(int j = 0; j < size; j++){
				Relation r = Relation.binary("R" + i + "," + j);
				relation.add(r);
				b.bound(r, tfac.noneOf(2), tfac.allOf(2));
			}
		}
		
		for(int i = 0; i < size * 2; i++){
			int min = (i < size) ? 0: i - size + 1;
			int max = (i < size) ? i: size - 1;
			int offset = i < size? 0: i - size + 1;
			
			temp = null;
			
			for(int j = min; j <= max; j++){
				Formula t = xy.in(relations.get(j).get(max - j + offset));
				temp = (temp == null) ? t: temp.or(t);
			}
			
			if(temp != null)
				f = (f == null) ? temp: f.and(temp);
		}
		
		f = f.forSome(x.oneOf(Expression.UNIV)).forSome(y.oneOf(Expression.UNIV));

		return new FormulaStruct(f, b);
	}	
	/**
	 * @param args
	 * @throws TrivialFormulaException 
	 * @throws ContradictionException 
	 * @throws TimeoutException 
	 */
	public static void main(String[] args) throws TrivialFormulaException, ContradictionException, TimeoutException {
		
		
		// Generating kodkod fmlas
		//FormulaStruct fs = formula1();
		//FormulaStruct fs = formula0();
		//FormulaStruct fs = formula2();
		FormulaStruct fs = formula3();
		//FormulaStruct fs = formula4();

		Formula fmla = fs.getFmla();
		Bounds b = fs.getBounds();
		
		MyReporter rep = new MyReporter();		
		
		// Invoking the solver		
		MinSolver solver = new MinSolver();
		solver.options().setFlatten(true);	
		solver.options().setSymmetryBreaking(0); // check we get 4 models not 2
		MinSATSolverFactory minimalFactory = new MinSATSolverFactory(rep);		
		solver.options().setSolver(minimalFactory);
		
		// tuple in upper bound ---> that tuple CAN appear in the relation
		// tuple in lower bound ---> tuple MUST appear in the relation
		
		solver.options().setReporter(rep);

		
		// Ask for models of R(x) satisfying those bounds, over that universe.
		// But kodkod only accepts SENTENCES. All vars must be bound:
		Iterator<MinSolution> models = solver.solveAll(fmla, b);
		/*MinSolution model = solver.solve(fmla, b); */
		 
		//for (int i = 0; i < 10; i++){
		int counter = 0;
		while(models.hasNext())
		{
			long currTime = System.currentTimeMillis();			
			MinSolution model = models.next();			
			
			if(MinSolution.Outcome.UNSATISFIABLE.equals(model.outcome()) ||
					MinSolution.Outcome.TRIVIALLY_UNSATISFIABLE.equals(model.outcome()))
				break;
			
			if(counter == 0)
			{				
				System.out.println("========================================================");
				System.out.println("FORMULA: " + fs.getFmla().toString());
				System.out.println("STATISTICS: ");
				System.out.println(model.stats().clauses()+" clauses.");
				System.out.println(model.stats().primaryVariables()+" primary variables.");
				System.out.println(model.stats().variables()+" total variables.");
				System.out.println(model.stats().translationTime()+" translation time.");
				System.out.println("========================================================\n");
			}
			
			// !!! question: how much of this delay in producing lifters is due to having to remove clauses?
			
			System.out.println("Minimal model: "+model.instance().relationTuples());
			System.out.println("Time to produce+print minimal model or UNSAT (ms): "+(System.currentTimeMillis()-currTime));
			currTime = System.currentTimeMillis();
						
			//TODO Cleanup the test code below:
			/*Map<Relation, TupleSet> results = solver.getLifters(models).relationTuples();			
			Iterator<Relation> it1 = fs.bounds.relations().iterator();
			while(it1.hasNext()){
				Relation r = it1.next();
				TupleSet tuples = results.get(r);				
				Iterator<Tuple> it2 = tuples.iterator();
				while(it2.hasNext()){
					Instance instance = new Instance(fs.bounds.universe());
					TupleSet s = fs.bounds.universe().factory().setOf(it2.next()); 
					
					instance.add(r, s);
					
					System.out.println("-------------------------------------------------------");
					System.out.println("Lifter:   " + instance.relationTuples());
					System.out.println("Model:    " + model.instance().relationTuples());
		
					Iterator<MinSolution> liftModels = 
							solver.lift(fs.fmla, fs.bounds, solver.getTranslation(models), model, instance);
					
					while(liftModels.hasNext()){
						MinSolution liftModel = liftModels.next();
						if(MinSolution.Outcome.UNSATISFIABLE.equals(liftModel.outcome()) ||
								MinSolution.Outcome.TRIVIALLY_UNSATISFIABLE.equals(liftModel.outcome()))
							break;						
						System.out.println("Lifted model:  " + liftModel.instance().relationTuples());
					}
					
				}
			}*/
			
			//System.out.println("Lifters: "+ solver.getLifters(models).relationTuples());
			
			
			
			System.out.println("Time to produce+print lifters (ms): "+(System.currentTimeMillis()-currTime));
			System.out.println("========================================================\n");
			counter++;
			
		}
		
		// If the fmla is unsatisfiable, you do get ONE solution in the iterator with:
		// sol.outcome.equals(Solution.UNSAT) or Solution.TRIVIALLY_UNSAT
		
		
		/*while(models.hasNext())
		{
			MinSolution amodel = models.next();
			System.out.println(amodel+"--------------------------------------------------------------------\n");
			counter ++;
		}*/
		
		System.out.println("Total minimal models seen: "+counter);
	}
}