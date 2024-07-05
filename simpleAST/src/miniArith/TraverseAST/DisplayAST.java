package miniArith.TraverseAST;

/** AST traversal to display fully parenthesized form of the AST
 *    Inherits - nothing (null)
 *    Synthesizes - String holding display form of the subtree rooted at this node
 */

import miniArith.AbstractSyntaxTrees.*;

public class DisplayAST implements Visitor<Object, String> {
	
    public String visitBinExpr(BinExpr e, Object arg){
    	return "(" + e.left.visit(this, null) 
    	+ " " + e.oper.spelling
        + " " + e.right.visit(this, null) + ")";
    }
    
    public String visitNumExpr(NumExpr e, Object arg) {
    	return e.num.spelling;
    }
}


