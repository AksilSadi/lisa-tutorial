package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.Variable;
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
}
