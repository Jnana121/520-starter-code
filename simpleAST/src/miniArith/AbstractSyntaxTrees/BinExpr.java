package miniArith.AbstractSyntaxTrees;

import miniArith.SyntacticAnalyzer.Token;

public class BinExpr extends Expr {
    public Token oper;
    public Expr left;
    public Expr right;

    public BinExpr(Expr left, Token oper, Expr right) {
        this.left = left;
        this.oper = oper;
        this.right = right;
    }
    
    public <Inh,Syn> Syn visit(Visitor<Inh,Syn> v, Inh arg) {
        return v.visitBinExpr(this, arg);
    }
}


