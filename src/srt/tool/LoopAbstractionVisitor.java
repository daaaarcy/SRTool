package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BinaryExpr;
import srt.ast.BlockStmt;
import srt.ast.DeclRef;
import srt.ast.EmptyStmt;
import srt.ast.Expr;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopAbstractionVisitor extends DefaultVisitor {

    List<String> modset = null;

    public LoopAbstractionVisitor() {
        super(true);
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        List<Stmt> list = new ArrayList<Stmt>();

        List<Expr> invs = whileStmt.getInvariantList().getExprs();
        Expr invariant = null;
        for (Expr e : invs) {
            if (invariant == null) {
                invariant = e;
            } else {
                invariant = new BinaryExpr(BinaryExpr.LAND, invariant, e);
            }
        }

        modset = new ArrayList<String>();
        visit(whileStmt.getBody());
        Stmt havocModset[] = new Stmt[modset.size()];
        for (int i = 0; i < havocModset.length; i++) {
            havocModset[i] = new HavocStmt(new DeclRef(modset.get(i)));

        }

        if (invariant != null)
            list.add(new AssertStmt(invariant));
        list.add(new BlockStmt(havocModset));
        if (invariant != null)
            list.add(new AssumeStmt(invariant));

        List<Stmt> ifBody = new ArrayList<Stmt>();
        ifBody.add(whileStmt.getBody());
        if (invariant != null)
            ifBody.add(new AssertStmt(invariant));
        ifBody.add(new AssumeStmt(new IntLiteral(0)));
        list.add(new IfStmt(whileStmt.getCondition(), new BlockStmt(ifBody),
                new EmptyStmt()));

        return new BlockStmt(list, whileStmt);
    }

    @Override
    public Object visit(AssignStmt assignment) {
        String var = assignment.getLhs().getName();
        if (modset != null && !modset.contains(var)) {
            modset.add(var);
        }
        return super.visit(assignment);
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        String var = havocStmt.getVariable().getName();
        if (modset != null && !modset.contains(var)) {
            modset.add(var);
        }
        return super.visit(havocStmt);
    }

}
