package minsolver.fol2sat;

import java.util.Set;

import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;

public class MinSymmetryDetectorDelegate {
	public static Set<IntSet> partition(Bounds bounds){
		return MinSymmetryDetector.partition(bounds);
	}
}
