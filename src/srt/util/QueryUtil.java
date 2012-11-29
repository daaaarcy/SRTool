package srt.util;

public abstract class QueryUtil {
	
	//Setters
	public static String SetLogicQF_BV = "(set-logic QF_BV)\n";
	
	//Definitions & their calls
	//------------------------------------------------------------provided to BV method
	public static String DefineTobv32 
	  ="(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";
	public static String tobv32 = "tobv32";
	//------------------------------------------------------------Logical Not for BV
	public static String DefineBVLNot 
	  = "(define-fun bvlnot ((p (_ BitVec 32))) (_ BitVec 32) (ite (= p (_ bv0 32)) (_ bv1 32) (_ bv0 32)))";
	public static String BVLNot = "bvlnot";
	//------------------------------------------------------------
	//convenient macros
	public static String TRUE = "(_ bv1 32)";
	
	

}
