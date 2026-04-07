package it.unive.lisa.tutorial;

import it.unive.lisa.AnalysisException;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.LiSA;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.heap.pointbased.FieldSensitivePointBasedHeap;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.conf.LiSAConfiguration.GraphType;
import it.unive.lisa.imp.IMPFrontend;
import it.unive.lisa.imp.ParsingException;
import it.unive.lisa.program.Program;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGe;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.type.Untyped;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class TwoVariableLinearInequalityTest {

	@Test
	public void assumeLessOrEqualStoresConstraint() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, 0);

		assertTrue(updated.getState(x).contains(expected));
		assertTrue(updated.getState(y).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assumeLessThanStoresStrictConstraint() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLt.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, -1);

		assertTrue(updated.getState(x).contains(expected));
		assertTrue(updated.getState(y).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assumeGreaterOrEqualStoresRewrittenConstraint() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonGe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, 0);

		assertTrue(updated.getState(x).contains(expected));
		assertTrue(updated.getState(y).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assumeGreaterThanStoresRewrittenStrictConstraint() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonGt.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, -1);

		assertTrue(updated.getState(x).contains(expected));
		assertTrue(updated.getState(y).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assumeEqualityStoresBothDirections() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonEq.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint xy =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, 0);
		TwoVariableLinearInequality.Constraint yx =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, 0);

		assertTrue(updated.getState(x).contains(xy));
		assertTrue(updated.getState(y).contains(xy));
		assertTrue(updated.getState(x).contains(yx));
		assertTrue(updated.getState(y).contains(yx));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void strictConstraintImpliesNonStrictOne() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression strict = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLt.INSTANCE,
				SyntheticLocation.INSTANCE);
		BinaryExpression nonStrict = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(strict, null, null, null);

		assertEquals(Satisfiability.SATISFIED, updated.satisfies(nonStrict, null, null));
	}

	@Test
	public void contradictoryStrictComparisonsYieldBottom() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression less = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLt.INSTANCE,
				SyntheticLocation.INSTANCE);
		BinaryExpression greater = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonGt.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(less, null, null, null)
				.assume(greater, null, null, null);

		assertTrue(updated.isBottom());
		assertEquals(Satisfiability.NOT_SATISFIED, domain.assume(less, null, null, null)
				.satisfies(greater, null, null));
	}

	@Test
	public void assignForgetsConstraintsMentioningAssignedVariable() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);
		Constant zero = new Constant(Untyped.INSTANCE, 0, SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null)
				.assign(x, zero, null, null);

		assertEquals(Satisfiability.UNKNOWN, updated.satisfies(condition, null, null));
		assertTrue(updated.getState(y).elements.isEmpty());
	}

	@Test
	public void forgetIdentifiersIfRemovesMatchingKeysAndConstraints() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null)
				.forgetIdentifiersIf(id -> id.equals(y));

		assertTrue(!updated.knowsIdentifier(y));
		assertEquals(Satisfiability.UNKNOWN, updated.satisfies(condition, null, null));
		assertTrue(updated.getState(x).elements.isEmpty());
	}

	@Test
	public void assignVariableStoresEqualityBothDirections() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression equality = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonEq.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assign(x, y, null, null);

		assertEquals(Satisfiability.SATISFIED, updated.satisfies(equality, null, null));
	}

	@Test
	public void assignAdditionStoresOffsetConstraints() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		Constant two = new Constant(Untyped.INSTANCE, 2, SyntheticLocation.INSTANCE);
		BinaryExpression expr = new BinaryExpression(
				Untyped.INSTANCE,
				y,
				two,
				AdditionOperator.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assign(x, expr, null, null);
		TwoVariableLinearInequality.Constraint xy =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, 2);
		TwoVariableLinearInequality.Constraint yx =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, -2);

		assertTrue(updated.getState(x).contains(xy));
		assertTrue(updated.getState(y).contains(xy));
		assertTrue(updated.getState(x).contains(yx));
		assertTrue(updated.getState(y).contains(yx));
	}

	@Test
	public void assignSubtractionStoresNegativeOffsetConstraints() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		Constant two = new Constant(Untyped.INSTANCE, 2, SyntheticLocation.INSTANCE);
		BinaryExpression expr = new BinaryExpression(
				Untyped.INSTANCE,
				y,
				two,
				SubtractionOperator.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assign(x, expr, null, null);
		TwoVariableLinearInequality.Constraint xy =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, -2);
		TwoVariableLinearInequality.Constraint yx =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, 2);

		assertTrue(updated.getState(x).contains(xy));
		assertTrue(updated.getState(y).contains(xy));
		assertTrue(updated.getState(x).contains(yx));
		assertTrue(updated.getState(y).contains(yx));
	}

	@Test
	public void assumeSupportsOffsetsOnTheRight() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		Constant two = new Constant(Untyped.INSTANCE, 2, SyntheticLocation.INSTANCE);
		BinaryExpression right = new BinaryExpression(
				Untyped.INSTANCE,
				y,
				two,
				AdditionOperator.INSTANCE,
				SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				right,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, 2);

		assertTrue(updated.getState(x).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assumeSupportsOffsetsOnTheLeft() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		Constant one = new Constant(Untyped.INSTANCE, 1, SyntheticLocation.INSTANCE);
		BinaryExpression left = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				one,
				AdditionOperator.INSTANCE,
				SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				left,
				y,
				ComparisonLt.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assume(condition, null, null, null);
		TwoVariableLinearInequality.Constraint expected =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, -2);

		assertTrue(updated.getState(x).contains(expected));
		assertEquals(Satisfiability.SATISFIED, updated.satisfies(condition, null, null));
	}

	@Test
	public void assignSupportsConstantOnTheLeftOfAddition() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		Constant two = new Constant(Untyped.INSTANCE, 2, SyntheticLocation.INSTANCE);
		BinaryExpression expr = new BinaryExpression(
				Untyped.INSTANCE,
				two,
				y,
				AdditionOperator.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality updated = domain.assign(x, expr, null, null);
		TwoVariableLinearInequality.Constraint xy =
				new TwoVariableLinearInequality.Constraint(x, y, 1, -1, 2);
		TwoVariableLinearInequality.Constraint yx =
				new TwoVariableLinearInequality.Constraint(y, x, 1, -1, -2);

		assertTrue(updated.getState(x).contains(xy));
		assertTrue(updated.getState(y).contains(yx));
	}

	@Test
	public void pushAndPopScopePreserveConstraints() throws Exception {
		TwoVariableLinearInequality domain = new TwoVariableLinearInequality();
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);
		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);
		ScopeToken token = new ScopeToken(() -> SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality scoped = domain.assume(condition, null, null, null).pushScope(token);
		Identifier scopedX = (Identifier) x.pushScope(token);
		Identifier scopedY = (Identifier) y.pushScope(token);
		BinaryExpression scopedCondition = new BinaryExpression(
				Untyped.INSTANCE,
				scopedX,
				scopedY,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		assertEquals(Satisfiability.SATISFIED, scoped.satisfies(scopedCondition, null, null));
		assertEquals(Satisfiability.SATISFIED, scoped.popScope(token).satisfies(condition, null, null));
	}

	@Test
	public void testTvpiAnalysis() throws ParsingException, AnalysisException {
		Program program = IMPFrontend.processFile("inputs/tvpi.imp");
		LiSAConfiguration conf = new DefaultConfiguration();
		conf.workdir = "outputs/tvpi";
		conf.analysisGraphs = GraphType.HTML;
		conf.abstractState = DefaultConfiguration.simpleState(
				new FieldSensitivePointBasedHeap(),
				new TwoVariableLinearInequality(),
				DefaultConfiguration.defaultTypeDomain());

		new LiSA(conf).run(program);
	}
}
