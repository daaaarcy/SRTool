package srt.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Node;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
    // Map containing the next index to use when renaming a new assignment to
    // each variable, keyed off the variable name.
    private Map<String, Integer> index = new HashMap<String, Integer>();

    public SSAVisitor() {
        super(true);
    }

    // The SSA name for variable N is N$i where i is the index of the current
    // renamed variable. A $ is used to ensure this is not an existing Simple C
    // variable name.
    private String getSSAName(String name) {
        return name + "$" + index.get(name);
    }

    // Mark that a new assignment has been made to variable "name" and so the
    // index to use in its SSA name should be increased.
    private void incrementSSAIndex(String name) {
        index.put(name, index.get(name) + 1);
    }

    @Override
    public Object visit(Decl decl) {
        // Replace this declaration with an SSA renamed equivalent.
        index.put(decl.getName(), 0);
        Decl renamed = new Decl(getSSAName(decl.getName()), decl.getType(),
                decl);
        return super.visit(renamed);
    }

    @Override
    public Object visit(DeclRef declRef) {
        // Replace this variable's name with its SSA renamed name.
        DeclRef renamed = new DeclRef(getSSAName(declRef.getName()), declRef);
        return super.visit(renamed);
    }

    @Override
    public Object visit(AssignStmt assignment) {
        // Visit the children of this assignment. The RHS is visited first as
        // we want this to use the old index of any variables, whereas the LHS
        // should use a new index for the variable we are assigning to.
        Node newRhs = (Node) visit(assignment.getRhs());
        incrementSSAIndex(assignment.getLhs().getName());
        Node newLhs = (Node) visit(assignment.getLhs());

        // Return the SSA renamed assignment in place of the original one.
        List<Node> children = new ArrayList<Node>();
        children.add(newLhs);
        children.add(newRhs);

        return assignment.withNewChildren(children);
    }

}
