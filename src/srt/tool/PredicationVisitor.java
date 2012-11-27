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
	private int freshPredInd = 0;
	private int freshVarInd = 0;

	public PredicationVisitor() {
		super(true);
	}
	
	@Override
	public Object visit(IfStmt ifStmt) {
		Stmt list[] = new Stmt[6];
		
		String freshQName = "$A" + freshPredInd;
		freshPredInd++;
		Decl freshQDeclare = new Decl(freshQName, "int");
		list[0] = freshQDeclare;
		DeclRef freshQVar = new DeclRef(freshQName);

		String freshRName = "$A" + freshPredInd;
		freshPredInd++;
		Decl freshRDeclare = new Decl(freshRName, "int");
		list[1] = freshRDeclare;
		DeclRef freshRVar = new DeclRef(freshRName);
		
		AssignStmt assignQ = new AssignStmt(freshQVar,
											new BinaryExpr(BinaryExpr.LAND,
														   currentPredicate,
														   ifStmt.getCondition())
										   );
		list[2] = assignQ;
		
		AssignStmt assignR = new AssignStmt(freshRVar,
											new BinaryExpr(BinaryExpr.LAND,
				  										   currentPredicate,
				  										   new UnaryExpr(UnaryExpr.LNOT, ifStmt.getCondition()))
										   );
		list[3] = assignR;
		
		Expr savedCurrent = currentPredicate;
		currentPredicate = freshQVar;
		list[4] = (Stmt) visit(ifStmt.getThenStmt());
		currentPredicate = freshRVar;
		list[5] = (Stmt) visit(ifStmt.getThenStmt());
		currentPredicate = savedCurrent;

		return new BlockStmt(list, ifStmt);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		TernaryExpr newAssert = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND, globalPredicate, currentPredicate), 
				 						 		assertStmt.getCondition(),
				 						 		new IntLiteral(1));

		List<Node> children = new ArrayList<Node>();
		children.add(newAssert);

		return assertStmt.withNewChildren(children);
	}

	@Override
	public Object visit(AssignStmt assignment) {
		TernaryExpr newRhs = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND, globalPredicate, currentPredicate), 
											 assignment.getRhs(),
											 assignment.getLhs());

		List<Node> children = new ArrayList<Node>();
		children.add(assignment.getLhs());
		children.add(newRhs);
		
		return assignment.withNewChildren(children);
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		Stmt list[] = new Stmt[2];
		
		String freshName = "$A" + freshPredInd;
		freshPredInd++;
		Decl freshDeclare = new Decl(freshName, "int");
		list[0] = freshDeclare;
		DeclRef freshVar = new DeclRef(freshName);
		
		TernaryExpr newAssume = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND, globalPredicate, currentPredicate),
												assumeStmt.getCondition(),
												new IntLiteral(1));
		AssignStmt newAssign = new AssignStmt(freshVar, newAssume, assumeStmt);
		list[1] = newAssign;
		
		globalPredicate = new BinaryExpr(BinaryExpr.LAND, globalPredicate, freshVar);
		
		return new BlockStmt(list, assumeStmt);
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		Stmt list[] = new Stmt[2];
		
		String freshName = "$h" + freshVarInd;
		freshVarInd++;
		Decl freshDeclare = new Decl(freshName, "int");
		list[0] = freshDeclare;
		DeclRef freshVar = new DeclRef(freshName);
		
		TernaryExpr newHavoc = new TernaryExpr(new BinaryExpr(BinaryExpr.LAND, globalPredicate, currentPredicate),
											   freshVar,
											   havocStmt.getVariable());
		AssignStmt newAssign = new AssignStmt(havocStmt.getVariable(), newHavoc, havocStmt);
		list[1] = newAssign;
		
		return new BlockStmt(list, havocStmt);
	}

}
