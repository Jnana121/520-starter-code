package miniArith.AbstractSyntaxTrees;

import miniArith.SyntacticAnalyzer.Token;

public class NumExpr extends Expr {
    public Token num;

    public NumExpr(Token num) {
        this.num = num;
    }
    
    public <Inh,Syn> Syn visit(Visitor<Inh,Syn> v, Inh arg) {
        return v.visitNumExpr(this, arg);
    }
}


