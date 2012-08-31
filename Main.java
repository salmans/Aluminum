import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.*;

import minsolver.*;

import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;


import kodkod.ast.*;
import kodkod.ast.visitor.*;
import kodkod.instance.*;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.fol2sat.TrivialFormulaException;

import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.opts.BooleanOption;
import org.kohsuke.args4j.opts.FileOption;
import org.kohsuke.args4j.opts.IntOption;
import org.kohsuke.args4j.opts.StringOption;

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


/*class CNFSpy implements SATSolver
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
    		//for(int ii=0;ii<wrapper.size();ii++)
    		//	for(int jj=ii+1;jj<wrapper.size();jj++)
    		//	{
    		//		if(Math.abs(wrapper.get(ii)) == Math.abs(wrapper.get(jj)))
    		//			MEnvironment.errorStream.println("TAUT");
    		//	}
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
*/
/*class CNFSpyFactory extends SATFactory
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
    
}*/



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

class OutputData{
	/**
	 * A list to store times to generate minimal models.
	 */
	int[] minimalTime;
	
	/**
	 * A list to store times to generate random models.
	 */
	int[] randomTime;
	
	/**
	 * A list to store the number of SAT solving iterations for computing
	 * minimal models. 
	 */
	int[] iterations;
	
	/**
	 * The size of the lists. 
	 */
	final int size;
	
	OutputData(int size){
		this.size = size;
		minimalTime = new int[size];
		randomTime = new int[size];
		iterations = new int[size];
		
		for(int i = 0; i < size; i++){
			minimalTime[i] = 0;
			randomTime[i] = 0;
			iterations[i] = 0;
		}
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

	private static FormulaStruct formula2(int length){
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
		
		
		for(int i = 0; i < length; i++){
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
	private static FormulaStruct formula3(int length){
		int size = length;
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
	private static FormulaStruct formula4(int length){
		int size = length;
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
	
	//Transitive Closure
	private static FormulaStruct formula5(){
		Variable x = Variable.unary("x");
		Variable y = Variable.unary("y");
		Variable z = Variable.unary("z");
		Variable x1 = Variable.unary("x1");
		Variable x2 = Variable.unary("x2");
		
		Expression xy = x.product(y);
		Expression xz = x.product(z);
		Expression zy = z.product(y);
		Expression x1x2 = x1.product(x2);
		
		Relation r = Relation.binary("R");
		Relation rTC = Relation.binary("R+"); 
		
		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("a");
		allPossibleAtoms.add("b");
		allPossibleAtoms.add("c");
		allPossibleAtoms.add("d");
		
		Universe u = new Universe(allPossibleAtoms);
		
		//Transitive closure
		Formula f = xy.in(r).implies(xy.in(rTC)).forAll(x.oneOf(Expression.UNIV)).forAll(y.oneOf(Expression.UNIV)) 
				.and((xz.in(r)).and(zy.in(rTC)).implies(xy.in(rTC)).
						forAll(x.oneOf(Expression.UNIV)).
						forAll(y.oneOf(Expression.UNIV)).
						forAll(z.oneOf(Expression.UNIV))).
				//The relation is not empty!
				and(x1x2.in(r).forSome(x1.oneOf(Expression.UNIV)).forSome(x2.oneOf(Expression.UNIV)));
		
		Bounds b = new Bounds(u);
		TupleFactory tfac = u.factory();
		//b.bound(r, tfac.noneOf(2), tfac.allOf(2));
		b.bound(r, tfac.range(tfac.tuple(2, 1), tfac.tuple(2, 4)), tfac.allOf(2));
		b.bound(rTC, tfac.noneOf(2), tfac.allOf(2));
				
		return new FormulaStruct(f, b);
	}

	/**
	 * Builds a formula from the content of a SATLib example file.
	 * @param fileName is the address of the example file.
	 * @return a formula
	 */
	private static FormulaStruct exampleFormula(String fileName){
		Variable x = Variable.unary("x");
		ExampleLoader example = new ExampleLoader(fileName);
		ArrayList<ArrayList<Integer>> data = example.getContent();
		
		ArrayList<Relation> relations = new ArrayList<Relation>();
	
		Set<String> allPossibleAtoms = new HashSet<String>();
		allPossibleAtoms.add("element0");
		allPossibleAtoms.add("element1");
		Universe u = new Universe(allPossibleAtoms);
	
		Bounds b = new Bounds(u);
		TupleFactory tfac = u.factory();
		
		Formula f = null;
		
		//Building relations:
		for(int i = 1; i <= example.getNumOfVars(); i++){
			Relation r = Relation.unary("R" + i);
			b.bound(r, tfac.noneOf(1), tfac.allOf(1));
			relations.add(r);
		}
		
		for(int i = 0; i < data.size(); i++){
			ArrayList<Integer> clause = data.get(i);
			Formula clauseFormula;
			clauseFormula = null;
			for(int j = 0; j < clause.size(); j++){
				int relation = clause.get(j);
				boolean negation = relation < 0;
				relation = (relation > 0)? relation: -relation;

				if(!negation){
					if(clauseFormula == null)
						clauseFormula = x.in(relations.get(relation - 1));
					else
						clauseFormula = clauseFormula.or(x.in(relations.get(relation - 1)));
				}
				else{
					if(clauseFormula == null)
						clauseFormula = x.in(relations.get(relation - 1)).not();
					else
						clauseFormula = clauseFormula.or(x.in(relations.get(relation - 1)).not());
				}
			}
			
			if(f == null)
				f = clauseFormula;
			else
				f = f.and(clauseFormula);
		}
		f = f.forSome(x.oneOf(Expression.UNIV));
		
		return new FormulaStruct(f, b);
	}
	
	/**
	 * Gets executed when parameter "-m formula" is passed to the program.
	 * @param optFormula parameter -f
	 * @param optAugmentation parameter -a 
	 * @param optLength parameter -l
	 * @throws TimeoutException
	 * @throws ContradictionException
	 */
	private static void formulaMode(IntOption optFormula,
			BooleanOption optAugmentation, IntOption optLength)
			throws TimeoutException, ContradictionException {
		// Generating kodkod fmlas
		if(!optFormula.isSet){
			System.err.println("No formula specified.");
			System.exit(0);
		}
		
		FormulaStruct fs = null;
		switch (optFormula.value){
			case 0: fs = formula0(); break;
			case 1: fs = formula1(); break;
			case 2: fs = formula2(optLength.value); break;
			case 3: fs = formula3(optLength.value); break;
			case 4: fs = formula4(optLength.value); break;
			case 5: fs = formula5(); break;
		}
		
		Formula fmla = fs.getFmla();
		Bounds b = fs.getBounds();
		
		MinReporterToGatherSkolemBounds rep = new MinReporterToGatherSkolemBounds();		
		
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
				System.out.println("Bounds: " + fs.getBounds().toString());
				System.out.println("-------------------------------------------------------\n");
				System.out.println("STATISTICS: ");
				System.out.println(model.stats().clauses()+" clauses.");
				System.out.println(model.stats().primaryVariables()+" primary variables.");
				System.out.println(model.stats().variables()+" total variables.");
				System.out.println(model.stats().translationTime()+" translation time.");
				System.out.println("========================================================\n");
				System.out.println("MODELS:");
			}
			
			// !!! question: how much of this delay in producing CFs is due to having to remove clauses?
			
			System.out.println("Minimal model: "+model.instance().relationTuples());
			System.out.println("Time to produce+print minimal model or UNSAT (ms): "+(System.currentTimeMillis()-currTime));
			currTime = System.currentTimeMillis();
						
			if(optAugmentation.isOn()){
				Map<Relation, TupleSet> results = solver.getConsistentFacts(models).relationTuples();			
				Iterator<Relation> it1 = results.keySet().iterator();
				while(it1.hasNext()){
					Relation r = it1.next();
					TupleSet tuples = results.get(r);				
					Iterator<Tuple> it2 = tuples.iterator();
					while(it2.hasNext()){
						Instance instance = new Instance(fs.bounds.universe());
						TupleSet s = fs.bounds.universe().factory().setOf(it2.next()); 
						
						instance.add(r, s);
						
						System.out.println("-------------------------------------------------------");
						System.out.println("Consistent Fact:   " + instance.relationTuples());
						System.out.println("Model:    " + model.instance().relationTuples());
						Iterator<MinSolution> augModels = null;
						try{
							augModels = solver.augment(fs.fmla, models, instance);
						}
						catch(ExplorationException e){
							System.err.println(e.getMessage());
							System.exit(0);
						}
						
						while(augModels.hasNext()){
							MinSolution augModel = augModels.next();
							if(MinSolution.Outcome.UNSATISFIABLE.equals(augModel.outcome()) ||
									MinSolution.Outcome.TRIVIALLY_UNSATISFIABLE.equals(augModel.outcome()))
								break;						
							System.out.println("Augmented model:  " + augModel.instance().relationTuples());
						}
						
					}
				}
			
			//System.out.println("Augmentations: "+ solver.getConsistentFacts(models).relationTuples());			
				System.out.println("Time to produce+print augmentations (ms): "+(System.currentTimeMillis()-currTime));
			}
			System.out.println("========================================================\n");
			counter++;
			
		}
		
		System.out.println("Total minimal models seen: "+counter);
	}
	
	/**
	 * Processing a single example file where "-m example".
	 * @param optInputFile the input file option.
	 * @param optOutputFile the output file option.
	 * @param optNumberOfModels the option corresponding to the number of models
	 * to generate.
	 */
	private static void exampleModeFile(FileOption optInputFile, 
			FileOption optOutputFile, IntOption optNumberOfModels) {
		if(optInputFile.value == null){
			System.err.println("No SATLib example file has been provided.");
			System.exit(0);
		}

		int numberOfModels = 0;
		if(optNumberOfModels.isSet)
			numberOfModels = optNumberOfModels.value;
		
		String inputFilePath = optInputFile.value.getAbsolutePath();
		String outputFilePath = null;
		if(optOutputFile.value != null)
			outputFilePath = optOutputFile.value.getAbsolutePath();
		else{
			String fileName = optInputFile.value.getName();
			fileName = fileName.substring(0, fileName.lastIndexOf('.'));
			fileName += ".dat";
			outputFilePath = optInputFile.value.getParentFile().
					getAbsolutePath() + File.separator + fileName;
		}
		
		exampleModeHelper(inputFilePath, outputFilePath, numberOfModels, null);
	}

	/**
	 * Processing the files in a directory where "-m example".
	 * @param optInputFile the input file option corresponding to the input directory.
	 * @param optOutputFile the output file option for the output directory.
	 * @param optNumberOfModels the option for the number of models to generate.
	 */
	private static void exampleModeDirectory(FileOption optInputFile, 
			FileOption optOutputFile, IntOption optNumberOfModels,
			FileOption optSummaryFile) {
		if(optInputFile.value == null){
			System.err.println("No SATLib example file has been provided.");
			System.exit(0);
		}
		if(optOutputFile.value != null){
			if(!optOutputFile.value.isDirectory()){
				System.err.println("The output has to be a path to a directory.");
				System.exit(0);
			}
		}
		
		int numberOfModels = 0;
		if(optNumberOfModels.isSet)
			numberOfModels = optNumberOfModels.value;
		
		String outputFilePath = null;
		if(optOutputFile.value != null)
			outputFilePath = optOutputFile.value.getAbsolutePath();
		else
			outputFilePath = optInputFile.value.getAbsolutePath();
		
		OutputData summary = null;
		if(optSummaryFile.value != null)
			summary = new OutputData(numberOfModels);
		
		File files[] = optInputFile.value.listFiles();
		for(int i = 0; i < files.length; i++){
			String fileName = files[i].getName();
			fileName = fileName.substring(0, fileName.lastIndexOf('.'));
			fileName += ".dat";
			
			System.out.print("Processing "+ files[i].getName() + "...");
			
			exampleModeHelper(
					files[i].getAbsolutePath(), 
					outputFilePath + File.separator + fileName, 
					numberOfModels, summary);
			
			System.out.println("done!");
		}

		if(optSummaryFile.value != null){
			//Writing the summary file:
			try{			
				FileWriter fstream = new FileWriter(optSummaryFile.value);
				BufferedWriter out = new BufferedWriter(fstream);
	
				// Writing the header row:
				out.write("iteration random minimal loops\n");
				// Writing data rows:
				for(int i = 1; i <= summary.size; i++){
					out.write(i + " " 
							+ summary.randomTime[i - 1] + " "
							+ summary.minimalTime[i - 1] + " "
							+ summary.iterations[i - 1] + "\n");				
				}
				
				out.close();
			}catch (Exception e){
				System.err.println("Error: " + e.getMessage());
			}
		}
	}
	
	/**
	 * Helper for example mode functions.
	 * @param inputFilePath the path of input example file.
	 * @param outputFilePath the path of output file.
	 * @param numberOfModels the number of models to generate.
	 * @param summary the input OutputData object to store a summary.
	 * @return the summary.
	 */
	private static OutputData exampleModeHelper(String inputFilePath,
			String outputFilePath, int numberOfModels, OutputData summary) {
		FormulaStruct fs = exampleFormula(inputFilePath);
		
		Formula fmla = fs.getFmla();
		Bounds bnds = fs.getBounds();
		
		MinReporterToGatherSkolemBounds rep = new MinReporterToGatherSkolemBounds();		
		
		// Invoking the solver
		MinSolver minSolver = new MinSolver();
		minSolver.options().setFlatten(true);
		
		//TODO parameterize symmetry breaking
		minSolver.options().setSymmetryBreaking(0);
		
		MinSATSolverFactory minimalFactory = new MinSATSolverFactory(rep);		
		minSolver.options().setSolver(minimalFactory);

		Solver solver = new Solver();
		solver.options().setFlatten(true);	
		solver.options().setSymmetryBreaking(0);
		
		minSolver.options().setReporter(rep);
		
		long currTime;

		ArrayList<Long> randomModelTimes = new ArrayList<Long>();
		ArrayList<Long> minimalModelTimes = new ArrayList<Long>();
		ArrayList<Integer> minimalModelIterations = new ArrayList<Integer>();		
		
		Iterator<MinSolution> minModels = minSolver.solveAll(fmla, bnds);
		
		//Generating minimal models:
		while(minModels.hasNext()){
			currTime = System.currentTimeMillis();
			MinSolution sol = minModels.next();
			minimalModelTimes.add(System.currentTimeMillis() - currTime);
			minimalModelIterations.add(sol.minimizationHistory.SATSolverInvocations);
			
			if(numberOfModels != 0){
				if(minimalModelTimes.size() == numberOfModels)
					break;
			}
		}	
		
		//Generating arbitrary models:
		Iterator<Solution> models = solver.solveAll(fmla, bnds);
		while(models.hasNext()){
			currTime = System.currentTimeMillis();
			models.next();
			randomModelTimes.add(System.currentTimeMillis() - currTime);

			if(randomModelTimes.size() == minimalModelTimes.size())
				break;
		}
		
		//Writing the output file:
		try{			
			FileWriter fstream = new FileWriter(outputFilePath);
			BufferedWriter out = new BufferedWriter(fstream);

			// Writing the header row:
			out.write("iteration random minimal loops\n");
			// Writing data rows:
			for(int i = 1; i <= minimalModelTimes.size(); i++){
				out.write(i + " " 
						+ randomModelTimes.get(i - 1) + " "
						+ minimalModelTimes.get(i - 1) + " "
						+ minimalModelIterations.get(i - 1) + "\n");
				
				if(summary != null){
					summary.minimalTime[i - 1] += minimalModelTimes.get(i - 1);
					summary.randomTime[i - 1] += randomModelTimes.get(i - 1);
					summary.iterations[i - 1] += minimalModelIterations.get(i - 1);
				}
			}
			
			out.close();
		}catch (Exception e){
			System.err.println("Error: " + e.getMessage());
		}
		
		return summary;
	}
	
	/**
	 * The main method of the demo program.
	 */
	public static void main(String[] args) throws TrivialFormulaException, ContradictionException, TimeoutException {
		//input formula ranging from 0 to 4. 
		IntOption optFormula = new IntOption("-f");
		BooleanOption optAugmentation = new BooleanOption("-a");
		IntOption optLength = new IntOption("-l", 10);
		StringOption optMode = new StringOption("-m", "formula");
		FileOption optInputFile = new FileOption("-i");
		FileOption optOutputFile = new FileOption("-o");
		IntOption optNumberOfModels = new IntOption("-n", 10);
		FileOption optSummaryFile = new FileOption("-s");
		
		CmdLineParser optParser = new CmdLineParser();
		optParser.addOption(optMode);		
		optParser.addOption(optFormula);
		optParser.addOption(optAugmentation);
		optParser.addOption(optLength);
		optParser.addOption(optInputFile);
		optParser.addOption(optOutputFile);
		optParser.addOption(optNumberOfModels);
		optParser.addOption(optSummaryFile);
		
		try{
			optParser.parse(args);
		}
		catch(CmdLineException e){
			System.err.println(e.getMessage());
		}
		
		if(optMode.value.equals("formula"))
			formulaMode(optFormula, optAugmentation, optLength);
		else{
			if(optInputFile.value.isDirectory())
				exampleModeDirectory(optInputFile, optOutputFile, 
						optNumberOfModels, optSummaryFile);
			else
				exampleModeFile(optInputFile, optOutputFile, optNumberOfModels);
		}
	}	
}