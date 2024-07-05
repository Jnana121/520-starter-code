package miniArith.SyntacticAnalyzer;

import java.io.*;
import miniArith.ErrorReporter;

/** Scanner to handle whitespace and scan the multi-character 
 *  num token.
 */  
public class Scanner {
    private char currentChar;
    private InputStream inputStream;
    private ErrorReporter reporter;
    private boolean eot = false;

    /** initialize scanner 
     */
    public Scanner(InputStream inputStream, ErrorReporter reporter) {
        this.inputStream = inputStream;
        this.reporter = reporter;
        nextChar();
    }

    /** scan the next token
     */
    public Token scan() {

        // scan separator
        while (!eot && currentChar == ' ') {
            nextChar();
        }

        // scan token
        TokenKind kind = TokenKind.EOF;
        StringBuffer spelling = new StringBuffer("");

        if (!eot) {
            switch (currentChar) {
            case '+': 
                kind = TokenKind.PLUS; 
                spelling.append(currentChar);
                nextChar(); 
                break;
                
            case '*':
                kind = TokenKind.TIMES; 
                spelling.append(currentChar);
                nextChar(); 
                break;

            case '(':
                kind = TokenKind.LPAREN; 
                spelling.append(currentChar);
                nextChar(); 
                break;

            case ')':
                kind = TokenKind.RPAREN; 
                spelling.append(currentChar);
                nextChar(); 
                break;

            case '0': case '1': case '2':
            case '3': case '4': case '5':
            case '6': case '7': case '8':
            case '9':
                kind = TokenKind.NUM;
                do {
                    spelling.append(currentChar);
                    nextChar();
                } while (!eot && isDigit(currentChar));
                break;

            default:
                spelling.append(currentChar);
                scanError("Unrecognized character in input: " + currentChar);
                kind = TokenKind.ERR; 
                nextChar();
                break;
            }
        }

        Token t = new Token(kind,spelling.toString());
        return t;
    }

    private void nextChar() {
        try { 
            int rr = inputStream.read(); 
            if (rr == -1) 
                eot = true;
            else {
                currentChar = (char) rr;
                // new line signals end of text
                if (currentChar == '\n' || currentChar == '\r')
                    eot = true;
            }
        } 
        catch (IOException e) { 
            eot = true;
        }
    }

    private boolean isDigit(char c) {
        return (c >= '0') && (c <= '9');
    }
    
    private void scanError(String m) {
    	reporter.reportError("Scan Error:  " + m);

    }
}
