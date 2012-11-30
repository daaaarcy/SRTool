package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BinaryExpr;
import srt.ast.BlockStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Node;
import srt.ast.Stmt;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class PredicationVisitor extends DefaultVisitor {

    private Expr globalPredicate = new IntLiteral(1);
    private Expr currentPredicate = new IntLiteral(1);

    // The next index to use for a fresh variable or predicate name.
    private int freshPredInd = 0;
    private int freshVarInd = 0;

    public PredicationVisitor() {
        super(true);
    }

    @Override
    public Object visit(IfStmt ifStmt) {
        List<Stmt> list = new ArrayList<Stmt>();

        // Declare a fresh predicate to use for the "then" branch.
        String freshQName = "$A" + freshPredInd;
        freshPredInd++;
        Decl freshQDeclare = new Decl(freshQName, "int");
        list.add(freshQDeclare);
        DeclRef freshQVar = new DeclRef(freshQName);

        // Declare a fresh predicate to use for the "else" branch.
        String freshRName = "$A" + freshPredInd;
        freshPredInd++;
        Decl freshRDeclare = new Decl(freshRName, "int");
        list.add(freshRDeclare);
        DeclRef freshRVar = new DeclRef(freshRName);

        // Assign the conjunction of the current predicate and the if condition
        // to the "then" branch fresh predicate.
        AssignStmt assignQ = new AssignStmt(freshQVar, new BinaryExpr(
                BinaryExpr.LAND, currentPredicate, ifStmt.getCondition()));
        list.add(assignQ);

        // Assign the conjunction of the current predicate and the negated if
        // condition to the "else" branch fresh predicate.
        AssignStmt assignR = new AssignStmt(freshRVar, new BinaryExpr(
                BinaryExpr.LAND, currentPredicate, new UnaryExpr(
                        UnaryExpr.LNOT, ifStmt.getCondition())));
        list.add(assignR);

        // Finally, visit the statements inside the if condition, setting the
        // appropriate predicate as the current predicate for each visit.
        Expr savedCurrent = currentPredicate;
        currentPredicate = freshQVar;
        list.add((Stmt) visit(ifStmt.getThenStmt()));
        currentPredicate = freshRVar;
        list.add((Stmt) visit(ifStmt.getElseStmt()));
        currentPredicate = savedCurrent;

        // Return these new statements we have defined in place of the if
        // statement.
        return new BlockStmt(list, ifStmt);
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        // Predicate the assert condition with the current and global predicates.
        TernaryExpr newAssert = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND,
                globalPredicate, currentPredicate), assertStmt.getCondition(),
                new IntLiteral(1));

        // Return the assert statement with the new, predicated condition as a
        // child.
        List<Node> children = new ArrayList<Node>();
        children.add(newAssert);

        return assertStmt.withNewChildren(children);
    }

    @Override
    public Object visit(AssignStmt assignment) {
        // Predicate the assignment so it only takes place if the current and
        // global predicates hold.
        TernaryExpr newRhs = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND,
                globalPredicate, currentPredicate), assignment.getRhs(),
                assignment.getLhs());

        // Return a new assignment with the predicated expression in place of
        // the previous expression.
        List<Node> children = new ArrayList<Node>();
        children.add(assignment.getLhs());
        children.add(newRhs);

        return assignment.withNewChildren(children);
    }

    @Override
    public Object visit(AssumeStmt assumeStmt) {
        Stmt list[] = new Stmt[2];

        // Declare a fresh predicate to add to the global predicate
        String freshName = "$A" + freshPredInd;
        freshPredInd++;
        Decl freshDeclare = new Decl(freshName, "int");
        list[0] = freshDeclare;
        DeclRef freshVar = new DeclRef(freshName);

        // Predicate the assume expression with the current and global
        // predicates and assign it to our fresh predicate.
        TernaryExpr newAssume = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND,
                globalPredicate, currentPredicate), assumeStmt.getCondition(),
                new IntLiteral(1));
        AssignStmt newAssign = new AssignStmt(freshVar, newAssume, assumeStmt);
        list[1] = newAssign;

        // Replace the global predicate with the conjunction of its previous
        // value and the fresh predicate.
        globalPredicate = new BinaryExpr(BinaryExpr.LAND, globalPredicate,
                freshVar);

        // Return these new statements in place of the assume statement.
        return new BlockStmt(list, assumeStmt);
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        Stmt list[] = new Stmt[2];

        // Declare a fresh variable that will represent the value produced by
        // havoc.
        String freshName = "$h" + freshVarInd;
        freshVarInd++;
        Decl freshDeclare = new Decl(freshName, "int");
        list[0] = freshDeclare;
        DeclRef freshVar = new DeclRef(freshName);

        // Only assign the fresh variable to the havoced variable if the current
        // and global predicates hold.
        TernaryExpr newHavoc = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND,
                globalPredicate, currentPredicate), freshVar,
                havocStmt.getVariable());
        AssignStmt newAssign = new AssignStmt(havocStmt.getVariable(),
                newHavoc, havocStmt);
        list[1] = newAssign;

        // Return these new statements in place of the havoc statement.
        return new BlockStmt(list, havocStmt);
    }

}
