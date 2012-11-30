package srt.util;

public abstract class QueryUtil {

    // Setters - default setting provided
    public static String SetLogicQF_BV = "(set-logic QF_BV)\n";
    
    /* function definitions & their calls
     * 
     * in each section provide: 
     * 1)static string for defining functions in smtlib
     * 2)a static method to return the expr that will use these functions
     * 
     * */
    // -------------------tobv32-----------------------------------
    // ToBV32 method - provided 
    public static String DefineTobv32 
        = "(define-fun tobv32 ((p Bool)) " +
          "(_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n";

    public static String tobv32(String logic) {
        return " (tobv32 " + logic + ")";
    }

    // ----------------BV Logical Not------------------------------
    // logical not for a BV - returns another BV
    public static String DefineBVLNot 
        = "(define-fun bvlnot ((p (_ BitVec 32)))" +
          " (_ BitVec 32) (tobv32 (= p (_ bv0 32))))\n";

    public static String bvlnot(String bv) {
        return " (bvlnot " + bv + ") ";
    }

    // ------------------BV to Bool--------------------------------
    // changes BV to bools for any function that requires a bool argument
    public static String DefineToBool 
        = "(define-fun tobool ((p (_ BitVec 32))) " +
          "Bool (not (= p (_ bv0 32))))\n";

    public static String tobool(String bv) {
        return " (tobool " + bv + ") ";
    }

    // ------------------------------------------------------------

    
    /* Convenient Methods
     * For any simple static string methods that can be used elsewhere  
     */
    
    //-----------Declare-------------------------------------------
    //simple string function to return declarations
    public static String declare(String var, String type) {
        return "(declare-fun " + var + " () " + type + " )\n";
    }
    
    // convenient macros
    public static String TRUE = "(_ bv1 32)";
    public static String FALSE = "(_ bv0 32)";
}
