package srt.util;

public abstract class QueryUtil {
	
	//Setters
	public static String SetLogicQF_BV = "(set-logic QF_BV)\n";
	
	//Definitions & their calls
	public static String DefineTobv32 ="(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";
	public static String tobv32 = "tobv32";
	public static String DefineBVLogicAnd = "(define-fun BVlogicand )";
	public static String BVlogicAnd = "BVlogicand";
	
	//convenient macros
	public static String TRUE = "(_ bv1 32)";
	
	

}
