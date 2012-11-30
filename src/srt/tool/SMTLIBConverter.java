package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;
import static srt.util.QueryUtil.*;

public class SMTLIBConverter {

    private ExprToSmtlibVisitor exprConverter;
    private StringBuilder query;
    private List<String> assertVars = new ArrayList<String>();

    /*
     * NOTE: Some methods in here come from QueryUtil
     * from the srt.util package 
     */
    
    public SMTLIBConverter(Set<String> variableNames,
            List<Expr> transitionExprs, List<Expr> propertyExprs) {

        if (propertyExprs.size() == 0) {
            throw new IllegalArgumentException("No assertions.");
        }

        exprConverter = new ExprToSmtlibVisitor();
        query = querySetUp();

        for (String varname : variableNames) {
            query = query.append(declare(varname, "(_ BitVec 32)"));
        }

        for (int i = 0; i < propertyExprs.size(); i++) {
            String assertVar = "prop" + i;
            query = query.append(declare(assertVar, "(Bool)"));
            assertVars.add(assertVar);
        }

        for (Expr trans : transitionExprs) {
            exprConverter.branched();
            query = query.append("(assert " + exprConverter.visit(trans)
                    + ")\n");
        }

        // sets propI variables to negated assertions of the simple c prog
        if (!propertyExprs.isEmpty()) {
            for (int i = 0; i < propertyExprs.size(); i++) {
                exprConverter.branched();
                query = query.append("(assert (= " + assertVars.get(i)
                        + " (not " + exprConverter.visit(propertyExprs.get(i))
                        + ")))\n");
            }

            /*
             * adds the assertion to check if any the above propI can be
             * satisfied.
             */
            query.append("(assert");
            StringBuilder end = new StringBuilder();
            for (int i = 0; i < propertyExprs.size(); i++) {
                exprConverter.branched();
                query = query.append(" (or " + assertVars.get(i));
                end.append(")");
            }
            query.append(end + ")\n");
        }

        /*
         * Checks the above assertions. If sat. then the prog has failed its
         * verification, else it passed
         */
        query.append("(check-sat)\n");

        // To find out which propI values are sat/unsat - for those that failed
        query.append("(get-value ( ");
        for (int i = 0; i < propertyExprs.size(); i++) {
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
                res.add(Integer.parseInt(result.substring(6,
                        result.indexOf("true") - 1)));
            }
        }

        return res;
    }

    private StringBuilder querySetUp() {
        // adding settings
        StringBuilder query = new StringBuilder(SetLogicQF_BV);

        // adding definitions
        query = query.append(DefineTobv32);
        query = query.append(DefineBVLNot);
        query = query.append(DefineToBool);

        return query;

    }
    
}
