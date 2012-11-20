package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {
	
	private ExprToSmtlibVisitor exprConverter;
	private StringBuilder query;
	private List<String> assertVars = new ArrayList<String>();
	
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

		for(int i = 0; i < propertyExprs.size(); i++) {
			String assertVar = "prop" + i;
			query = query.append("(declare-fun "+ assertVar +" () (Bool))\n");
			assertVars.add(assertVar);
		}
		
		for(Expr trans : transitionExprs){
			exprConverter.branched();
			query = query.append("(assert " + exprConverter.visit(trans) + ")\n");
		}
		
		if(!propertyExprs.isEmpty()){
			for(int i = 0; i < propertyExprs.size(); i++) {
				exprConverter.branched();
				query = query.append("(assert (= " + assertVars.get(i) +
						" (not " + exprConverter.visit(propertyExprs.get(i)) + ")))\n");			
			}
			
			query.append("(assert");
			StringBuilder end = new StringBuilder();
			for(int i = 0; i < propertyExprs.size(); i++) {
				exprConverter.branched();
				query = query.append(" (or " + assertVars.get(i));
				end.append(")");
			}
			query.append(end + ")\n");
		}
		
		query.append("(check-sat)\n");
		
		query.append("(get-value ( ");
		for(int i = 0; i < propertyExprs.size(); i++) {
			query.append(assertVars.get(i) + " ");
		}
		query.append("))\n");
		
	}
	
	public String getQuery() {
		return query.toString();
	}
	
	public List<Integer> getPropertiesThatFailed(String queryResult) {
		List<Integer> res = new ArrayList<Integer>();
		
		String results[] = queryResult.split("\n");
		for (String result : results) {
			if (result.contains("true")) {
				res.add(Integer.parseInt(result.substring(6, result.indexOf("true") - 1)));
			}
		}
		
		return res;
	}
	
}
