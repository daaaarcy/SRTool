package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {
	
	private ExprToSmtlibVisitor exprConverter;
	private StringBuilder query;
	
	public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {
		
		if(propertyExprs.size() == 0)
		{
			throw new IllegalArgumentException("No assertions.");
		}
		
		exprConverter = new ExprToSmtlibVisitor();
		query = new StringBuilder("(set-logic QF_BV)\n" +
				"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		// TODO: Define more functions above (for convenience), as needed.

		// TODO: Declare variables, add constraints, add properties to check
		// here.
		for(String varname : variableNames){
			String entry 
				= "(declare-fun "+ varname +" () (_ BitVec 32))\n";
			query = query.append(entry);
		}
		
		for(Expr trans : transitionExprs){
			exprConverter.branched();
			query = query.append("(assert " + exprConverter.visit(trans) + ")\n");
		}
		
		if(!propertyExprs.isEmpty()){
		
			query.append("(assert \n");
			StringBuilder end = new StringBuilder();
			for(Expr prop : propertyExprs){
				exprConverter.branched();
				query = query.append("(or ( not " 
						+ exprConverter.visit(prop) 
						+ ")\n");
				end.append(")");
			}
			query.append(end + ")\n");
		}
		
		query.append("(check-sat)\n");
		
	}
	
	public String getQuery() {
		return query.toString();
	}
	
	public List<Integer> getPropertiesThatFailed(String queryResult) {
		List<Integer> res = new ArrayList<Integer>();
		
		return res;
	}
	
}
