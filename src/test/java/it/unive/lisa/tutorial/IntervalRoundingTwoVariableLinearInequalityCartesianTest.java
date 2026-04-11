package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGe;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.type.Untyped;
import it.unive.lisa.util.numeric.MathNumber;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class IntervalRoundingTwoVariableLinearInequalityCartesianTest {

	@Test
	public void intervalBoundsPropagateToRelationalComponent() throws Exception {
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Identifier y = new Variable(Untyped.INSTANCE, "y", SyntheticLocation.INSTANCE);

		ValueEnvironment<IntervalRounding> intervals = new ValueEnvironment<>(new IntervalRounding());
		intervals = intervals.putState(x, new IntervalRounding(new MathNumber(0), new MathNumber(0), MathNumber.ZERO));
		intervals = intervals.putState(y, new IntervalRounding(new MathNumber(2), new MathNumber(2), MathNumber.ZERO));

		IntervalRoundingTwoVariableLinearInequalityCartesian product =
				new IntervalRoundingTwoVariableLinearInequalityCartesian().mk(
						new TwoVariableLinearInequality(),
						intervals);

		BinaryExpression condition = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				y,
				ComparisonLt.INSTANCE,
				SyntheticLocation.INSTANCE);

		assertEquals(Satisfiability.SATISFIED,
				product.getRelationalComponent().satisfies(condition, null, null));
	}

	@Test
	public void relationalUnaryBoundsRefineIntervalComponent() throws Exception {
		Identifier x = new Variable(Untyped.INSTANCE, "x", SyntheticLocation.INSTANCE);
		Constant two = new Constant(Untyped.INSTANCE, 2, SyntheticLocation.INSTANCE);
		Constant five = new Constant(Untyped.INSTANCE, 5, SyntheticLocation.INSTANCE);

		BinaryExpression ge = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				two,
				ComparisonGe.INSTANCE,
				SyntheticLocation.INSTANCE);
		BinaryExpression le = new BinaryExpression(
				Untyped.INSTANCE,
				x,
				five,
				ComparisonLe.INSTANCE,
				SyntheticLocation.INSTANCE);

		TwoVariableLinearInequality relations = new TwoVariableLinearInequality()
				.assume(ge, null, null, null)
				.assume(le, null, null, null);

		IntervalRoundingTwoVariableLinearInequalityCartesian product =
				new IntervalRoundingTwoVariableLinearInequalityCartesian().mk(
						relations,
						new ValueEnvironment<>(new IntervalRounding()));

		IntervalRounding refined = product.getIntervalComponent().getState(x);

		assertTrue(refined.toValueInterval().low.geq(new MathNumber(2)));
		assertTrue(refined.toValueInterval().high.leq(new MathNumber(5)));
	}
}
