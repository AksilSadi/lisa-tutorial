package it.unive.lisa.tutorial;

import java.math.BigDecimal;
import java.text.NumberFormat;

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


/**
 * Basic interval operations can be found at
 * https://en.wikipedia.org/wiki/Interval_arithmetic#Interval_operators
 *
 * Lattice operators can be found in https://doi.org/10.1016/j.scico.2009.04.004
 */
public class IntervalRounding
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a single
		// variable
		// - they provide logic for the evaluation of expressions
		implements BaseNonRelationalValueDomain<
				// java requires this type parameter to have this class
				// as type in fields/methods
				IntervalRounding> {

	public static final IntervalRounding ZERO = new IntervalRounding(MathNumber.ZERO, MathNumber.ZERO, MathNumber.ZERO);
	public static final IntervalRounding TOP = new IntervalRounding(MathNumber.MINUS_INFINITY, MathNumber.PLUS_INFINITY,
			MathNumber.PLUS_INFINITY);
	public static final IntervalRounding BOTTOM = new IntervalRounding(MathNumber.NaN, MathNumber.NaN, MathNumber.NaN);

	public static final MathNumber EPS = new MathNumber(1e-9);
	public static final MathNumber MINUS_ONE = MathNumber.MINUS_ONE;

	public final IntervalReal interval;
	public final IntervalReal absErr;

	public IntervalRounding(
			IntervalReal interval,
			IntervalReal absErr) {
		this.interval = interval;
		this.absErr = absErr;
	}

	public IntervalRounding(
			MathNumber low,
			MathNumber high,
			MathNumber absErr) {
		this.interval = new IntervalReal(low, high);
		this.absErr = new IntervalReal(absErr.multiply(MathNumber.MINUS_ONE), absErr);
	}

	public IntervalRounding(
			MathNumber low,
			MathNumber high) {
		this(low, high, MathNumber.ZERO);
	}

	public IntervalRounding(
			MathNumber high) {
		this(MathNumber.MINUS_INFINITY, high);
	}

	public IntervalRounding() {
		this(MathNumber.MINUS_INFINITY, MathNumber.PLUS_INFINITY);
	}

	public MathNumber getRepError(Number n) {
		if (n instanceof Double)
			return new MathNumber(Math.ulp(n.doubleValue()) / 2.0);
		if (n instanceof Float)
			return new MathNumber(Math.ulp(n.floatValue()) / 2.0f);
		return new MathNumber(0.0);
	}

	@Override
	public IntervalRounding top() {
		// the top element of the lattice
		// if this method does not return a constant value,
		// you must override the isTop() method!
		return TOP;
	}

	@Override
	public IntervalRounding bottom() {
		// the bottom element of the lattice
		// if this method does not return a constant value,
		// you must override the isBottom() method!
		return BOTTOM;
	}

	public IntervalReal toValueInterval() {
		return this.interval.add(this.absErr);
	}

	@Override
	public boolean lessOrEqualAux(
			IntervalRounding other)
			throws SemanticException {
		return this.toValueInterval().lessOrEqualAux(other.toValueInterval());
	}

	@Override
	public IntervalRounding lubAux(
			IntervalRounding other)
			throws SemanticException {
		IntervalReal interval = this.interval.lubAux(other.interval);
		IntervalReal absErr = this.absErr.lubAux(other.absErr);
		return new IntervalRounding(interval, absErr);
	}

	@Override
	public IntervalRounding glbAux(
			IntervalRounding other) {
		IntervalReal interval = this.interval.glbAux(other.interval);
		IntervalReal absErr = this.absErr.glbAux(other.absErr);
		return new IntervalRounding(interval, absErr);
	}

	@Override
	public IntervalRounding wideningAux(
			IntervalRounding other)
			throws SemanticException {
		IntervalReal interval = this.interval.wideningAux(other.interval);
		IntervalReal absErr = this.absErr.wideningAux(other.absErr);
		return new IntervalRounding(interval, absErr);
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
		return "Values=" + interval.toString() + ", abs error=" + absErr.toString();
	}

	// logic for evaluating expressions below

	@Override
	public IntervalRounding evalNonNullConstant(
			Constant constant,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (constant.getValue() instanceof Integer) {
			Integer i = (Integer) constant.getValue();
			return new IntervalRounding(new MathNumber(i), new MathNumber(i), getRepError(i));
		} else if (constant.getValue() instanceof Float) {
			Float f = (Float) constant.getValue();
			return new IntervalRounding(new MathNumber(f), new MathNumber(f), getRepError(f));
		} else if (constant.getValue() instanceof Double) {
			Double d = (Double) constant.getValue();
			return new IntervalRounding(new MathNumber(d), new MathNumber(d), getRepError(d));
		}

		return top();
	}

	public IntervalRounding intervalNegation() {
		IntervalReal interval = this.interval.intervalNegation();
		IntervalReal absErr = this.absErr.intervalNegation();
		return new IntervalRounding(interval, absErr);
	}

	public IntervalRounding intervalStringLength() {
		return new IntervalRounding(MathNumber.ZERO, MathNumber.PLUS_INFINITY, MathNumber.ZERO);
	}

	@Override
	public IntervalRounding evalUnaryExpression(
			UnaryOperator operator,
			IntervalRounding arg,
			ProgramPoint pp,
			SemanticOracle oracle) {

		if (operator == NumericNegation.INSTANCE)
			return arg.intervalNegation();

		if (operator == StringLength.INSTANCE)
			return arg.intervalStringLength();

		return top();
	}

	public IntervalRounding add(IntervalRounding other) {
		IntervalReal interval = this.interval.add(other.interval);
		IntervalReal absErr = this.absErr.add(other.absErr);
		return new IntervalRounding(interval, absErr);
	}

	public IntervalRounding sub(IntervalRounding other) {
		IntervalReal interval = this.interval.sub(other.interval);
		IntervalReal absErr = this.absErr.sub(other.absErr);
		return new IntervalRounding(interval, absErr);
	}

	public IntervalRounding mul(IntervalRounding other) {
		/**
		 * (a+e)*(b+f) 
		 * = a*b + (a*f + e*b + e*f)
		 */
		IntervalReal valuesInterval = this.interval.mul(other.interval);

		IntervalReal leftErrorInterval = this.absErr.mul(other.interval);
		IntervalReal rightErrorInterval = this.interval.mul(other.absErr);
		IntervalReal mulErrorInterval = this.absErr.mul(other.absErr);

		IntervalReal combinedErrorInterval = leftErrorInterval.add(rightErrorInterval).add(mulErrorInterval);

		return new IntervalRounding(valuesInterval, combinedErrorInterval);
	}

	public IntervalRounding div(IntervalRounding other) {
		/**
		 * 1 / (b + f) 
		 * = (1 / b)*(1 - (f / (b+f)))
		 * = (1 / b) + (-(f/b)/(f+b))	
		 * 
		 * (a + e) / (b + f)
		 * = (a + e) * (1 / (b + f))		
		 */

		IntervalReal int_fpb = other.toValueInterval();
		IntervalReal int_fbb = other.absErr.div(other.interval).intervalNegation();
		IntervalReal err_inv = int_fbb.div(int_fpb);

		IntervalRounding denomIntervalRounding = new IntervalRounding(other.interval.inv(), err_inv);

		return this.mul(denomIntervalRounding);
	}

	@Override
	public IntervalRounding evalBinaryExpression(
			BinaryOperator operator,
			IntervalRounding left,
			IntervalRounding right,
			ProgramPoint pp,
			SemanticOracle oracle) {
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

	public Satisfiability eq(IntervalRounding other) {
		return this.toValueInterval().eq(other.toValueInterval());
	}

	public Satisfiability neq(IntervalRounding other) {
		return this.toValueInterval().neq(other.toValueInterval());
	}

	public Satisfiability lt(IntervalRounding other) {
		return this.toValueInterval().lt(other.toValueInterval());
	}

	public Satisfiability le(IntervalRounding other) {
		return this.toValueInterval().le(other.toValueInterval());
	}

	@Override
	public Satisfiability satisfiesBinaryExpression(
			BinaryOperator operator,
			IntervalRounding left,
			IntervalRounding right,
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
	public ValueEnvironment<IntervalRounding> assumeBinaryExpression(
			ValueEnvironment<IntervalRounding> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle)
			throws SemanticException {
		Identifier id;
		IntervalRounding eval;
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

		IntervalRounding starting = environment.getState(id);
		if (eval.isBottom() || starting.isBottom())
			return environment.bottom();

		IntervalReal theoryIntervalReal = eval.interval;

		boolean lowIsMinusInfinity = theoryIntervalReal.low.isMinusInfinity();
		IntervalRounding low_inf = new IntervalRounding(new IntervalReal(theoryIntervalReal.low, MathNumber.PLUS_INFINITY), eval.absErr);
		IntervalRounding lowp1_inf = new IntervalRounding(new IntervalReal(theoryIntervalReal.low.add(EPS), MathNumber.PLUS_INFINITY), eval.absErr);
		IntervalRounding inf_high = new IntervalRounding(new IntervalReal(MathNumber.MINUS_INFINITY, theoryIntervalReal.high), eval.absErr);
		IntervalRounding inf_highm1 = new IntervalRounding(new IntervalReal(MathNumber.MINUS_INFINITY, theoryIntervalReal.high.subtract(EPS)), eval.absErr);

		IntervalRounding update = null;
		if (operator == ComparisonEq.INSTANCE)
			update = eval;
		else if (operator == ComparisonGe.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
			else
				update = starting.glb(inf_high);
		else if (operator == ComparisonGt.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);
			else
				update = lowIsMinusInfinity ? eval : starting.glb(inf_highm1);
		else if (operator == ComparisonLe.INSTANCE)
			if (rightIsExpr)
				update = starting.glb(inf_high);
			else
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
		else if (operator == ComparisonLt.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? eval : starting.glb(inf_highm1);
			else
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);

		if (update == null)
			return environment;
		else if (update.isBottom())
			return environment.bottom();
		else
			return environment.putState(id, update);
	}
}