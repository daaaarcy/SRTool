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
    private Map<String, Integer> index = new HashMap<String, Integer>();

    public SSAVisitor() {
        super(true);
    }

    private String getSSAName(String name) {
        return name + "$" + index.get(name);
    }

    private void incrementSSAIndex(String name) {
        index.put(name, index.get(name) + 1);
    }

    @Override
    public Object visit(Decl decl) {
        index.put(decl.getName(), 0);
        Decl renamed = new Decl(getSSAName(decl.getName()), decl.getType(),
                decl);
        return super.visit(renamed);
    }

    @Override
    public Object visit(DeclRef declRef) {
        DeclRef renamed = new DeclRef(getSSAName(declRef.getName()), declRef);
        return super.visit(renamed);
    }

    @Override
    public Object visit(AssignStmt assignment) {
        Node newRhs = (Node) visit(assignment.getRhs());
        incrementSSAIndex(assignment.getLhs().getName());
        Node newLhs = (Node) visit(assignment.getLhs());

        List<Node> children = new ArrayList<Node>();
        children.add(newLhs);
        children.add(newRhs);

        return assignment.withNewChildren(children);
    }

}
