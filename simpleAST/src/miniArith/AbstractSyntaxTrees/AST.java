package miniArith.AbstractSyntaxTrees;

/** AST: Abstract Syntax Tree
 *    Expr ::=   Expr Oper Expr         (BinExpr)
 *             | Num                    (NumExpr)
 */
public abstract class AST { 
    
    public abstract <Inh,Syn> Syn visit(Visitor<Inh,Syn> v, Inh o);
}



