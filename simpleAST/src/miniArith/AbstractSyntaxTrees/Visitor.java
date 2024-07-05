package miniArith.AbstractSyntaxTrees;

/**
 * An implementation of the Visitor interface provides a method visitX
 * for each non-abstract AST class X.  
 */
public interface Visitor<Inh,Syn> {
	// Expressions
	public Syn visitBinExpr(BinExpr expr, Inh arg);
	public Syn visitNumExpr(NumExpr expr, Inh arg);
}


