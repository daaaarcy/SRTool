package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;

public class LoopUnwinderVisitor extends DefaultVisitor
{

    private boolean unwindingAssertions;
    private int defaultUnwindBound;

    public LoopUnwinderVisitor(boolean unwindingAssertions,
                               int defaultUnwindBound)
    {
        super(true);
        this.unwindingAssertions = unwindingAssertions;
        this.defaultUnwindBound = defaultUnwindBound;
    }

    @Override
    public Object visit(WhileStmt whileStmt)
    {
        final IntLiteral bound = whileStmt.getBound();
        final Expr condition = whileStmt.getCondition();
        final Stmt body = whileStmt.getBody();
        final ExprList invList = whileStmt.getInvariantList();

        final int unwindBound = bound != null ? bound.getValue()
                : defaultUnwindBound;

        ArrayList<Stmt> truncStmts = new ArrayList<Stmt>();
        for (Expr inv : invList.getExprs())
        {
            truncStmts.add(new AssertStmt(inv));
        }

        // If no more unwinding is required, either assume or assert the negated
        // loop condition based on the global settings.
        if (unwindBound == 0)
        {

            final UnaryExpr notCond = new UnaryExpr(UnaryExpr.LNOT, condition);

            if (unwindingAssertions)
            {
                truncStmts.add(new AssertStmt(notCond));
            }

            truncStmts.add(new AssumeStmt(notCond));
            return new BlockStmt(truncStmts);
        }

        // Define a new while statement with the same properties as the previous
        // statement except with an unwind bound that is smaller by one. 
        final WhileStmt nextWhileStmt = new WhileStmt(condition,
                new IntLiteral(unwindBound - 1), invList,
                body);

        // Visit the new while loop recursively and return a while statement
        // unwound the given number of times.
        final Stmt[] unwindStmts = new Stmt[]{body,
                (Stmt) visit(nextWhileStmt)};
        return new IfStmt(condition, new BlockStmt(unwindStmts),
                new EmptyStmt());
    }

}
