package minkodkod;

/**
 * Indicates a problem with augmentation or consistent-fact generation.
 * @author Tim 
 *
 */
public class ExplorationException extends Exception {
	private static final long serialVersionUID = 1L;

	public ExplorationException(String msg){
		super(msg);
	}
}
