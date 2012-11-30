package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;

public class LoopUnwinderVisitor extends DefaultVisitor {

    private boolean unwindingAssertions;
    private int defaultUnwindBound;

    public LoopUnwinderVisitor(boolean unwindingAssertions,
                               int defaultUnwindBound) {
        super(true);
        this.unwindingAssertions = unwindingAssertions;
        this.defaultUnwindBound = defaultUnwindBound;
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        final IntLiteral bound = whileStmt.getBound();
        final Expr condition = whileStmt.getCondition();
        final Stmt body = whileStmt.getBody();

        final int unwindBound = bound != null ? bound.getValue() : defaultUnwindBound;

        if (unwindBound == 0) {
            ArrayList<Stmt> truncStmts = new ArrayList<Stmt>();

            final UnaryExpr notCond = new UnaryExpr(UnaryExpr.LNOT, condition);

            if (unwindingAssertions) {
                truncStmts.add(new AssertStmt(notCond));
            }

            truncStmts.add(new AssumeStmt(notCond));

            return new BlockStmt(truncStmts);
        }

        final WhileStmt nextWhileStmt = new WhileStmt(
                condition,
                new IntLiteral(unwindBound - 1),
                whileStmt.getInvariantList(),
                body
        );

        final Stmt[] unwindStmts = new Stmt[]{body, (Stmt) visit(nextWhileStmt)};
        return new IfStmt(condition, new BlockStmt(unwindStmts), new EmptyStmt());
    }

}
