package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.util.numeric.MathNumber;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class IntervalRealTest {

	@Test
	public void lessOrEqualIsInclusive() throws SemanticException {
		IntervalReal left = new IntervalReal(new MathNumber(1), new MathNumber(2));
		IntervalReal right = new IntervalReal(new MathNumber(1), new MathNumber(2));

		assertTrue(left.lessOrEqual(right));
	}

	@Test
	public void divisionByIntervalContainingZeroYieldsTop() {
		IntervalReal left = new IntervalReal(new MathNumber(1), new MathNumber(2));
		IntervalReal right = new IntervalReal(new MathNumber(-1), new MathNumber(1));

		assertTrue(left.div(right).isTop());
	}

	@Test
	public void lessOrEqualComparisonHandlesSharedBoundary() {
		IntervalReal left = new IntervalReal(new MathNumber(1), new MathNumber(1));
		IntervalReal right = new IntervalReal(new MathNumber(1), new MathNumber(2));

		assertEquals(Satisfiability.SATISFIED, left.le(right));
	}

	@Test
	public void arithmeticWidensFiniteBoundsForRounding() {
		IntervalReal left = new IntervalReal(new MathNumber(0.1), new MathNumber(0.1));
		IntervalReal right = new IntervalReal(new MathNumber(0.2), new MathNumber(0.2));
		IntervalReal result = left.add(right);

		assertTrue(result.low.lt(new MathNumber(0.3)));
		assertTrue(result.high.gt(new MathNumber(0.3)));
	}
}
