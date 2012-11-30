package srt.tool;

import srt.ast.BinaryExpr;
import srt.util.QueryUtil;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.IntLiteral;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class ExprToSmtlibVisitor extends DefaultVisitor {
	
	public boolean assertStat = false;
	
	
	public ExprToSmtlibVisitor() {
		super(false);
	}

	@Override
	public String visit(BinaryExpr expr) {
		String operator;
		boolean logicop = false;
		switch(expr.getOperator())
		{
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
				
			case BinaryExpr.LAND:
				logicop = true;
                operator = "(and "+ QueryUtil.tolog("%s") + QueryUtil.tolog("%s") + ")";
				break;
			case BinaryExpr.LOR:
				logicop = true;
                operator = "(or" + QueryUtil.tolog("%s") + QueryUtil.tolog("%s") + ")";
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
		if(!assertStat && logicop){
			operator = QueryUtil.tobv32(operator);
		}
		assertStat = false;
		return String.format(operator, visit(expr.getLhs()), visit(expr.getRhs()));
		
	}

	public void branched(){
		assertStat = true;
	}
	
	@Override
	public String visit(DeclRef declRef) {
		return !assertStat?
				declRef.getName()
				:"(= " + declRef.getName() +
					" " + QueryUtil.TRUE + " )";
	}

	@Override
	public String visit(IntLiteral intLiteral) {
		return "(_ bv" + intLiteral.getValue() + " 32)";

	}

	@Override
	public String visit(TernaryExpr ternaryExpr) {
		boolean oldAssertStat = assertStat;
		assertStat = true;
		String cond = visit(ternaryExpr.getCondition());
		assertStat = false;
		String trueExpr = visit(ternaryExpr.getTrueExpr());
		String falseExpr = visit(ternaryExpr.getFalseExpr());
		String result = "(ite " + cond +
				" " + trueExpr +
				" " + falseExpr + ")"; 
		return oldAssertStat? QueryUtil.tolog(result) :result;
	}

	@Override
	public String visit(UnaryExpr unaryExpr) {
		String operator = null;
		switch(unaryExpr.getOperator())
		{
		case UnaryExpr.UMINUS:
			operator = "(bvneg %s)";
			break;
		case UnaryExpr.UPLUS:
			operator = "%s";
			break;
		case UnaryExpr.LNOT:
			if(!assertStat){
				operator = QueryUtil.bvlnot(" %s");
			}else{
				operator = "(not %s)";
			}
			break;
		case UnaryExpr.BNOT:
			operator = "(bvnot %s)";
			break;
		default:
			throw new IllegalArgumentException("Invalid binary operator");
		}
		assertStat = false;
		return String.format(operator, visit(unaryExpr.getOperand()));
	}
	
	
	/* Overridden just to make return type String. 
	 * @see srt.ast.visitor.DefaultVisitor#visit(srt.ast.Expr)
	 */
	@Override
	public String visit(Expr expr) {
		return (String) super.visit(expr);
	}
	
	

}
