package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.program.SyntheticLocation;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.Variable;
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
}
