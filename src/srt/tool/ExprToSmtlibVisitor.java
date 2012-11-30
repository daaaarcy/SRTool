package srt.tool;

import srt.ast.BinaryExpr;
import static srt.util.QueryUtil.*;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.IntLiteral;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class ExprToSmtlibVisitor extends DefaultVisitor {

    /* This boolean is used as a flag to indicate if the "outer" operator requires
     * a bool - i.e. assert, the conditions in the ite function 
     */
    private boolean boolRequired = false;

    public ExprToSmtlibVisitor() {
        super(false);
    }

    /*
     * NOTE: Some methods in all the visit methods come from QueryUtil
     * from the srt.util package 
     */
    
    @Override
    public String visit(BinaryExpr expr) {
        String operator;
        // logicop is used to tell if the operator will return a Bool in smt
        boolean logicop = false;
        switch (expr.getOperator()) {
        case BinaryExpr.ADD:
            operator = "(bvadd %s %s)";
            break;
        case BinaryExpr.BAND:
            operator = "(bvand %s %s)";
            break;
        case BinaryExpr.BOR:
            operator = "(bvor %s %s)";
            break;
        case BinaryExpr.BXOR:
            operator = "(bvxor %s %s)";
            break;
        case BinaryExpr.DIVIDE:
            operator = "(bvsdiv %s %s)";
            break;
        case BinaryExpr.LSHIFT:
            operator = "(bvshl %s %s)";
            break;
        case BinaryExpr.MOD:
            operator = "(bvsmod %s %s)";
            break;
        case BinaryExpr.MULTIPLY:
            operator = "(bvmul %s %s)";
            break;
        case BinaryExpr.RSHIFT:
            operator = "(bvashr %s %s)";
            break;
        case BinaryExpr.SUBTRACT:
            operator = "(bvsub %s %s)";
            break;
            
            /* All logical functions including not func. below will assume that
             * their nested expression will give off a BV, tobool is a function
             * we defined to convert BVs to their respective bool values: 
             *      if the values is not 0 its true else false
             */
        case BinaryExpr.LAND:
            logicop = true;
            operator = "(and " + tobool("%s") + tobool("%s")
                    + ")";
            break;
        case BinaryExpr.LOR:
            logicop = true;
            operator = "(or" + tobool("%s") + tobool("%s")
                    + ")";
            break;
        case BinaryExpr.GEQ:
            logicop = true;
            operator = "(bvsge %s %s)";
            break;
        case BinaryExpr.GT:
            logicop = true;
            operator = "(bvsgt %s %s)";
            break;
        case BinaryExpr.LEQ:
            logicop = true;
            operator = "(bvsle %s %s)";
            break;
        case BinaryExpr.LT:
            logicop = true;
            operator = "(bvslt %s %s)";
            break;
        case BinaryExpr.NEQUAL:
            logicop = true;
            operator = "(not (= %s %s))";
            break;
        case BinaryExpr.EQUAL:
            logicop = true;
            operator = "(= %s %s)";
            break;
        default:
            throw new IllegalArgumentException("Invalid binary operator");
        }
        /* In general all smt bools are in BV form so if a bool is not
         * required and the result is a bool, it'll be converted into a BV
         */
        if (!boolRequired && logicop) {
            operator = tobv32(operator);
        }
        
        // By visiting "sub" operators, we will not require bools
        boolRequired = false;
        return String.format(operator, visit(expr.getLhs()),
                visit(expr.getRhs()));

    }

    // a public function to set the flag that a bool is required
    public void branched() {
        boolRequired = true;
    }

    @Override
    public String visit(DeclRef declRef) {
        // reference for something thats been declared
        return !boolRequired ? declRef.getName() : "(= " + declRef.getName()
                + " " + TRUE + " )";
    }

    @Override
    public String visit(IntLiteral intLiteral) {
        //There will be cases where the BV by itself is required to be a bool
        String result = "(_ bv" + intLiteral.getValue() + " 32)";
        return boolRequired ? tobool(result) : result;

    }

    /*since exploring nested expr can get messy in that the 
     * boolRequired flag could be required for both then and else exprs and
     * both may not return the same type, we make both return BV before deciding
     * to return either to convert to a bool or keep it as a BV 
     */
    @Override
    public String visit(TernaryExpr ternaryExpr) {
        boolean oldAssertStat = boolRequired;
        // we require that the condition gives back a bool
        boolRequired = true;
        String cond = visit(ternaryExpr.getCondition());
        
        boolRequired = false;
        String trueExpr = visit(ternaryExpr.getTrueExpr());
        String falseExpr = visit(ternaryExpr.getFalseExpr());
        String result = "(ite " + cond + " " + trueExpr + " " + falseExpr + ")";
        return oldAssertStat ? tobool(result) : result;
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        String operator = null;
        switch (unaryExpr.getOperator()) {
        case UnaryExpr.UMINUS:
            operator = "(bvneg %s)";
            break;
        case UnaryExpr.UPLUS:
            operator = "%s";
            break;
         // returns a BV "boolean" 
        case UnaryExpr.LNOT:
            operator = bvlnot(" %s");
            break;
        case UnaryExpr.BNOT:
            operator = "(bvnot %s)";
            break;
        default:
            throw new IllegalArgumentException("Invalid binary operator");
        }
        
        // converts values to their bool values if needed
        if (boolRequired) {
            operator = tobool(operator);
        }
        boolRequired = false;
        return String.format(operator, visit(unaryExpr.getOperand()));
    }

    /*
     * Overridden just to make return type String.
     * 
     * @see srt.ast.visitor.DefaultVisitor#visit(srt.ast.Expr)
     */
    @Override
    public String visit(Expr expr) {
        return (String) super.visit(expr);
    }

}
