package miniArith.TraverseAST;

/** AST traversal to evaluate the arithmetic expression represented by the AST
 *   Inherited - none (null)
 *   Synthesized - Integer evaluation of the subtree rooted at this node
 */

import miniArith.AbstractSyntaxTrees.*;

public class EvalAST implements Visitor<Object,Integer> {
    public Integer visitBinExpr(BinExpr e, Object arg){
    	
    	// evaluate left subtree
    	Integer lval = e.left.visit(this, null);
    	
    	// evaluate right subtree
    	Integer rval = e.right.visit(this, null);
    	
    	// evaluate binary operation between two results
        switch (e.oper.kind) {
        case PLUS:
            return lval + rval;

        case TIMES:
            return lval * rval;

        default:
        	assert false;
            return 0;
        }
    }
    
    public Integer visitNumExpr(NumExpr e, Object arg) {
    	
    	// leaf node yields integer value of the spelling
    	return Integer.parseInt(e.num.spelling);
    }
	
}


