package miniArith;

/**  COMP 520 - Arithmetic expression evaluator 
 *     Scan and parse input, construct AST. 
 *     Display and evaluate AST.
 */
import miniArith.AbstractSyntaxTrees.AST;
import miniArith.AbstractSyntaxTrees.Visitor;
import miniArith.SyntacticAnalyzer.Parser;
import miniArith.SyntacticAnalyzer.Scanner;
import miniArith.TraverseAST.DisplayAST;
import miniArith.TraverseAST.EvalAST;


public class Evaluator {
    private static Scanner scanner;
    private static Parser parser;
    private static ErrorReporter reporter;
    private static AST ast;

    public static void main(String[] args) {

    	// scan, parse, and build AST
        System.out.print("Enter Expression: ");
        reporter = new ErrorReporter();
        scanner = new Scanner(System.in, reporter);
        parser  = new Parser(scanner, reporter);
        ast = parser.parse();
        
        if (reporter.hasErrors()) 
        	return;
        
        // traverse AST to construct explicitly parenthesized text representation
        Visitor<Object,String> display = new DisplayAST();
        String textRepr = ast.visit(display,null);

        // traverse AST to evaluate its value
        Visitor<Object,Integer> eval = new EvalAST();
        int result = ast.visit(eval, null);
        
        // show result
        System.out.println(textRepr + " = " + result);
    }
}