package srt.util;

public abstract class QueryUtil {
	
	//Setters
	public static String SetLogicQF_BV = "(set-logic QF_BV)\n";
	
	//Definitions & their calls
	//------------------------------------------------------------provided to BV method
	public static String DefineTobv32 
	  ="(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";
	public static String tobv32(String logic){
		return " (tobv32 " + logic + ")";
	}
	//------------------------------------------------------------Logical Not for BV
	public static String DefineBVLNot 
	  = "(define-fun bvlnot ((p (_ BitVec 32))) (_ BitVec 32) (tobv32 (= p (_ bv0 32))))\n";
	public static String bvlnot(String bv){
		return " (bvlnot " + bv + ") ";
	}
	//------------------------------------------------------------Logical and for BV
	public static String DefineToLogic
	  = "(define-fun tolog ((p (_ BitVec 32))) Bool (not (= p (_ bv0 32))))\n";
	public static String tolog(String bv){
		return " (tolog " + bv + ") ";
	}	
	//------------------------------------------------------------
	
	//convenient macros
	public static String TRUE = "(_ bv1 32)"; 
	
	

}
