package minkodkod.engine.fol2sat;

import java.util.Set;

import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;

// ALUMINUM: exists to avoid making SymmetryDetector public

/**
 * Allow access to the SymmetryDetector class from minalloy package
 * @author salman
 *
 */
public class MinSymmetryDetectorDelegate {
	public static Set<IntSet> partition(Bounds bounds){
		return SymmetryDetector.partition(bounds);
	}
}
