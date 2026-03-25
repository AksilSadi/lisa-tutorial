package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.symbolic.value.operator.unary.StringLength;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.numeric.MathNumber;
import it.unive.lisa.util.numeric.MathNumberConversionException;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Objects;

/**
 * Basic interval operations can be found at
 * https://en.wikipedia.org/wiki/Interval_arithmetic#Interval_operators
 *
 * Lattice operators can be found in https://doi.org/10.1016/j.scico.2009.04.004
 */
public class IntervalReal
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a single
		// variable
		// - they provide logic for the evaluation of expressions
		implements BaseNonRelationalValueDomain<
				// java requires this type parameter to have this class
				// as type in fields/methods
				IntervalReal> {

	public static final IntervalReal ZERO = new IntervalReal(MathNumber.ZERO, MathNumber.ZERO);
	public static final IntervalReal TOP = new IntervalReal(MathNumber.MINUS_INFINITY, MathNumber.PLUS_INFINITY);
	public static final IntervalReal BOTTOM = new IntervalReal(MathNumber.NaN, MathNumber.NaN);

	public static final MathNumber EPS = new MathNumber(1e-9);
	public static final MathNumber MINUS_ONE = MathNumber.MINUS_ONE;

	/*
	 * In order to consider many types of rounding errors, we will give the bounds
	 * of
	 * the intervals, as well as a relative and absolute error measures that will
	 * depend
	 * on the type of variables modelled.
	 * 
	 * For instance, integer types will have no rounding errors, and different
	 * floating
	 * point types will have different rounding errors
	 */
	public final MathNumber low;
	public final MathNumber high;

	public IntervalReal(
			MathNumber low,
			MathNumber high) {
		this.low = low;
		this.high = high;
	}

	public IntervalReal(
			MathNumber high) {
		this(MathNumber.MINUS_INFINITY, high);
	}

	public IntervalReal() {
		this(MathNumber.MINUS_INFINITY, MathNumber.PLUS_INFINITY);
	}

	public MathNumber getRepError(Number n) {
		if (n instanceof Double)
			return new MathNumber(Math.ulp(n.doubleValue()) / 2.0);
		if (n instanceof Float)
			return new MathNumber(Math.ulp(n.floatValue()) / 2.0f);
		return new MathNumber(0.0);
	}

	private MathNumber roundLower(
			MathNumber value) {
		if (!value.isFinite())
			return value;

		try {
			return new MathNumber(Math.nextDown(value.toDouble()));
		} catch (MathNumberConversionException e) {
			return value;
		}
	}

	private MathNumber roundUpper(
			MathNumber value) {
		if (!value.isFinite())
			return value;

		try {
			return new MathNumber(Math.nextUp(value.toDouble()));
		} catch (MathNumberConversionException e) {
			return value;
		}
	}

	private IntervalReal roundedInterval(
			MathNumber low,
			MathNumber high) {
		if (low.isNaN() || high.isNaN())
			return top();

		MathNumber roundedLow = roundLower(low);
		MathNumber roundedHigh = roundUpper(high);
		if (roundedLow.compareTo(roundedHigh) > 0)
			return bottom();
		return new IntervalReal(roundedLow, roundedHigh);
	}

	private boolean containsZero() {
		return low.leq(MathNumber.ZERO) && high.geq(MathNumber.ZERO);
	}

	@Override
	public IntervalReal top() {
		// the top element of the lattice
		// if this method does not return a constant value,
		// you must override the isTop() method!
		return TOP;
	}

	@Override
	public IntervalReal bottom() {
		// the bottom element of the lattice
		// if this method does not return a constant value,
		// you must override the isBottom() method!
		return BOTTOM;
	}

	@Override
	public boolean lessOrEqualAux(
			IntervalReal other)
			throws SemanticException {
		return other.low.leq(low) && other.high.geq(high);
	}

	@Override
	public IntervalReal lubAux(
			IntervalReal other)
			throws SemanticException {
		MathNumber newLow = low.min(other.low);
		MathNumber newHigh = high.max(other.high);
		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new IntervalReal(newLow, newHigh);
	}

	@Override
	public IntervalReal glbAux(
			IntervalReal other) {
		MathNumber newLow = low.max(other.low);
		MathNumber newHigh = high.min(other.high);

		if (newLow.compareTo(newHigh) > 0)
			return bottom();
		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new IntervalReal(newLow, newHigh);
	}

	@Override
	public IntervalReal wideningAux(
			IntervalReal other)
			throws SemanticException {
		MathNumber newLow, newHigh;
		if (other.high.compareTo(high) > 0)
			newHigh = MathNumber.PLUS_INFINITY;
		else
			newHigh = high;

		if (other.low.compareTo(low) < 0)
			newLow = MathNumber.MINUS_INFINITY;
		else
			newLow = low;

		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new IntervalReal(newLow, newHigh);
	}

	@Override
	public StructuredRepresentation representation() {
		// this method serializes instances of this domain
		// to a json-compatible format that will be used for dumping
		if (isBottom())
			return Lattice.bottomRepresentation();

		if (isTop())
			return Lattice.topRepresentation();

		return new StringRepresentation(toString());
	}

	@Override
	public String toString() {
		return "[" + low + ", " + high + "]";
	}

	// logic for evaluating expressions below

	@Override
	public IntervalReal evalNonNullConstant(
			Constant constant,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (constant.getValue() instanceof Integer) {
			Integer i = (Integer) constant.getValue();
			return new IntervalReal(new MathNumber(i), new MathNumber(i));
		} else if (constant.getValue() instanceof Float) {
			Float f = (Float) constant.getValue();
			return new IntervalReal(new MathNumber(f), new MathNumber(f));
		} else if (constant.getValue() instanceof Double) {
			Double d = (Double) constant.getValue();
			return new IntervalReal(new MathNumber(d), new MathNumber(d));
		}

		return top();
	}

	public IntervalReal intervalNegation(IntervalReal arg) {
		if (arg.isTop())
			return top();
		return roundedInterval(arg.high.multiply(MINUS_ONE), arg.low.multiply(MINUS_ONE));
	}

	public IntervalReal intervalStringLength(IntervalReal arg) {
		return new IntervalReal(MathNumber.ZERO, MathNumber.PLUS_INFINITY);
	}

	@Override
	public IntervalReal evalUnaryExpression(
			UnaryOperator operator,
			IntervalReal arg,
			ProgramPoint pp,
			SemanticOracle oracle) {

		if (operator.equals(NumericNegation.INSTANCE))
			return intervalNegation(arg);

		if (operator.equals(StringLength.INSTANCE))
			return intervalStringLength(arg);

		return top();
	}

	public IntervalReal add(IntervalReal other) {
		return roundedInterval(low.add(other.low), high.add(other.high));
	}

	public IntervalReal sub(IntervalReal other) {
		return roundedInterval(low.subtract(other.high), high.subtract(other.low));
	}

	public IntervalReal mul(IntervalReal other) {

		MathNumber ll = low.multiply(other.low);
		MathNumber lh = low.multiply(other.high);
		MathNumber hl = high.multiply(other.low);
		MathNumber hh = high.multiply(other.high);

		MathNumber lb = ll.min(lh).min(hl).min(hh);
		MathNumber ub = ll.max(lh).max(hl).max(hh);

		return roundedInterval(lb, ub);
	}

	public IntervalReal div(IntervalReal other) {
		if (other.equals(ZERO))
			return bottom();

		// If divisor might be 0, a precise interval can become disjoint. We
		// conservatively over-approximate it with top.
		if (other.containsZero())
			return top();

		if (this.isTop())
			return top();

		IntervalReal divFactorInt = new IntervalReal(MathNumber.ONE.divide(other.high),
				MathNumber.ONE.divide(other.low));
		return this.mul(divFactorInt);

	}

	@Override
	public IntervalReal evalBinaryExpression(
			BinaryOperator operator,
			IntervalReal left,
			IntervalReal right,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (left.isBottom() || right.isBottom())
			return bottom();

		if (!(operator instanceof DivisionOperator) && (left.isTop() || right.isTop()))
			return top();

		if (operator instanceof AdditionOperator)
			return left.add(right);

		if (operator instanceof SubtractionOperator)
			return left.sub(right);

		if (operator instanceof MultiplicationOperator)
			return left.mul(right);

		if (operator instanceof DivisionOperator)
			return left.div(right);

		return top();
	}

	public Satisfiability eq(IntervalReal other) {
		try {
			IntervalReal glb = this.glb(other);
			if (glb.isBottom())
				return Satisfiability.NOT_SATISFIED;
		} catch (SemanticException e) {
			return Satisfiability.UNKNOWN;
		}

		if (this.low.equals(this.high) && this.equals(other))
			return Satisfiability.SATISFIED;

		return Satisfiability.UNKNOWN;
	}

	public Satisfiability neq(IntervalReal other) {
		return eq(other).negate();
	}

	public Satisfiability lt(IntervalReal other) {
		if (high.lt(other.low))
			return Satisfiability.SATISFIED;
		if (low.geq(other.high))
			return Satisfiability.NOT_SATISFIED;
		return Satisfiability.UNKNOWN;
	}

	public Satisfiability le(IntervalReal other) {
		if (high.leq(other.low))
			return Satisfiability.SATISFIED;
		if (low.gt(other.high))
			return Satisfiability.NOT_SATISFIED;
		return Satisfiability.UNKNOWN;
	}

	@Override
	public Satisfiability satisfiesBinaryExpression(
			BinaryOperator operator,
			IntervalReal left,
			IntervalReal right,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (left.isTop() || right.isTop())
			return Satisfiability.UNKNOWN;

		if (operator.equals(ComparisonEq.INSTANCE))
			return left.eq(right);

		if (operator.equals(ComparisonLt.INSTANCE))
			return left.lt(right);

		if (operator.equals(ComparisonGt.INSTANCE))
			return left.le(right).negate();

		if (operator.equals(ComparisonLe.INSTANCE))
			return left.le(right);

		if (operator.equals(ComparisonGe.INSTANCE))
			return left.lt(right).negate();

		if (operator.equals(ComparisonNe.INSTANCE))
			return left.neq(right);

		return Satisfiability.UNKNOWN;
	}

	@Override
	public ValueEnvironment<IntervalReal> assumeBinaryExpression(
			ValueEnvironment<IntervalReal> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle)
			throws SemanticException {
		Identifier id;
		IntervalReal eval;
		boolean rightIsExpr;
		if (left instanceof Identifier) {
			eval = eval(right, environment, src, oracle);
			id = (Identifier) left;
			rightIsExpr = true;
		} else if (right instanceof Identifier) {
			eval = eval(left, environment, src, oracle);
			id = (Identifier) right;
			rightIsExpr = false;
		} else
			return environment;

		IntervalReal starting = environment.getState(id);
		if (eval.isBottom() || starting.isBottom())
			return environment.bottom();

		boolean lowIsMinusInfinity = eval.low.isMinusInfinity();

		// TODO: Change the EPS with open and closed intervals
		IntervalReal low_inf = new IntervalReal(eval.low, MathNumber.PLUS_INFINITY);
		IntervalReal lowp1_inf = new IntervalReal(eval.low.add(EPS), MathNumber.PLUS_INFINITY);
		IntervalReal inf_high = new IntervalReal(MathNumber.MINUS_INFINITY, eval.high);
		IntervalReal inf_highm1 = new IntervalReal(MathNumber.MINUS_INFINITY, eval.high.subtract(EPS));

		IntervalReal update = null;

		if (operator == ComparisonEq.INSTANCE) {
			update = starting.glb(eval);
		} else if (operator.equals(ComparisonGe.INSTANCE)) {
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
			else
				update = starting.glb(inf_high);
		} else if (operator.equals(ComparisonGt.INSTANCE)) {
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);
			else
				update = starting.glb(inf_highm1);
		} else if (operator.equals(ComparisonLe.INSTANCE)) {
			if (rightIsExpr)
				update = starting.glb(inf_high);
			else
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
		} else if (operator.equals(ComparisonLt.INSTANCE)) {
			if (rightIsExpr)
				update = starting.glb(inf_highm1);
			else
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);
		}

		if (update == null)
			return environment;
		else if (update.isBottom())
			return environment.bottom();
		else
			return environment.putState(id, update);
	}

}
