package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.util.numeric.MathNumber;
import it.unive.lisa.util.numeric.MathNumberConversionException;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.HashSet;
import java.util.Set;

public class IntervalRoundingTwoVariableLinearInequalityCartesian
		extends CartesianProduct<
				IntervalRoundingTwoVariableLinearInequalityCartesian,
				TwoVariableLinearInequality,
				ValueEnvironment<IntervalRounding>,
				ValueExpression,
				Identifier>
		implements ValueDomain<IntervalRoundingTwoVariableLinearInequalityCartesian> {

	public IntervalRoundingTwoVariableLinearInequalityCartesian() {
		this(new TwoVariableLinearInequality(), new ValueEnvironment<>(new IntervalRounding()));
	}

	public IntervalRoundingTwoVariableLinearInequalityCartesian(
			TwoVariableLinearInequality left,
			ValueEnvironment<IntervalRounding> right) {
		super(left, right);
	}

	@Override
	public boolean knowsIdentifier(
			Identifier id) {
		return left.knowsIdentifier(id) || right.knowsIdentifier(id);
	}

	@Override
	public IntervalRoundingTwoVariableLinearInequalityCartesian mk(
			TwoVariableLinearInequality left,
			ValueEnvironment<IntervalRounding> right) {
		IntervalRoundingTwoVariableLinearInequalityCartesian product =
				new IntervalRoundingTwoVariableLinearInequalityCartesian(left, right);
		try {
			return product.reduce();
		} catch (SemanticException | MathNumberConversionException e) {
			return product;
		}
	}

	public TwoVariableLinearInequality getRelationalComponent() {
		return left;
	}

	public ValueEnvironment<IntervalRounding> getIntervalComponent() {
		return right;
	}

	private IntervalRoundingTwoVariableLinearInequalityCartesian reduce()
			throws SemanticException, MathNumberConversionException {
		TwoVariableLinearInequality reducedRelations = reduceIntervalsToRelations(right, left);
		ValueEnvironment<IntervalRounding> reducedIntervals = reduceRelationsToIntervals(right, reducedRelations);
		return new IntervalRoundingTwoVariableLinearInequalityCartesian(reducedRelations, reducedIntervals);
	}

	private TwoVariableLinearInequality reduceIntervalsToRelations(
			ValueEnvironment<IntervalRounding> intervals,
			TwoVariableLinearInequality relations)
			throws MathNumberConversionException {
		TwoVariableLinearInequality result = relations;
		Set<Identifier> identifiers = userVariables(intervals.getKeys());

		for (Identifier id : identifiers) {
			IntervalRounding state = intervals.getState(id);
			if (state.isTop() || state.isBottom())
				continue;

			IntervalReal values = state.toValueInterval();
			if (!values.low.isFinite() || !values.high.isFinite() || values.low.isNaN() || values.high.isNaN())
				continue;

			int lower = values.low.roundUp().toInt();
			int upper = values.high.roundDown().toInt();
			if (lower > upper)
				return result.bottom();

			result = result.addConstraint(new TwoVariableLinearInequality.Constraint(id, null, 1, 0, upper));
			result = result.addConstraint(new TwoVariableLinearInequality.Constraint(id, null, -1, 0, -lower));
		}

		for (Identifier x : identifiers) {
			IntervalRounding xState = intervals.getState(x);
			if (xState.isTop() || xState.isBottom())
				continue;

			IntervalReal xValues = xState.toValueInterval();
			if (!xValues.high.isFinite() || xValues.high.isNaN())
				continue;

			int xUpper = xValues.high.roundDown().toInt();
			for (Identifier y : identifiers) {
				if (x.equals(y))
					continue;

				IntervalRounding yState = intervals.getState(y);
				if (yState.isTop() || yState.isBottom())
					continue;

				IntervalReal yValues = yState.toValueInterval();
				if (!yValues.low.isFinite() || yValues.low.isNaN())
					continue;

				int yLower = yValues.low.roundUp().toInt();
				if (xUpper < yLower)
					result = result.addConstraint(new TwoVariableLinearInequality.Constraint(x, y, 1, -1, -1));
			}
		}

		return result;
	}

	private ValueEnvironment<IntervalRounding> reduceRelationsToIntervals(
			ValueEnvironment<IntervalRounding> intervals,
			TwoVariableLinearInequality relations)
			throws SemanticException {
		ValueEnvironment<IntervalRounding> result = intervals;
		for (TwoVariableLinearInequality.Constraint constraint : relations.getConstraints()) {
			if (constraint.left == null || constraint.right != null || !isUserVariable(constraint.left))
				continue;

			if (constraint.leftCoeff > 0) {
				int upper = floorDiv(constraint.constant, constraint.leftCoeff);
				IntervalRounding bound = new IntervalRounding(MathNumber.MINUS_INFINITY, new MathNumber(upper),
						MathNumber.ZERO);
				result = intersectInterval(result, constraint.left, bound);
			} else if (constraint.leftCoeff < 0) {
				int lower = ceilDiv(constraint.constant, constraint.leftCoeff);
				IntervalRounding bound = new IntervalRounding(new MathNumber(lower), MathNumber.PLUS_INFINITY,
						MathNumber.ZERO);
				result = intersectInterval(result, constraint.left, bound);
			}
		}

		return result;
	}

	private ValueEnvironment<IntervalRounding> intersectInterval(
			ValueEnvironment<IntervalRounding> environment,
			Identifier id,
			IntervalRounding bound)
			throws SemanticException {
		IntervalRounding current = environment.getState(id);
		if (current.isBottom())
			return environment.bottom();

		IntervalRounding refined = current.glb(bound);
		if (refined.isBottom())
			return environment.bottom();
		return environment.putState(id, refined);
	}

	private Set<Identifier> userVariables(
			Set<Identifier> identifiers) {
		Set<Identifier> result = new HashSet<>();
		for (Identifier id : identifiers)
			if (isUserVariable(id))
				result.add(id);
		return result;
	}

	private boolean isUserVariable(
			Identifier id) {
		String name = id.getName();
		return !name.contains("@") && !name.contains("pp") && !name.equals("this") && !name.contains("heap");
	}

	private int floorDiv(
			int left,
			int right) {
		return Math.floorDiv(left, right);
	}

	private int ceilDiv(
			int left,
			int right) {
		return -Math.floorDiv(-left, right);
	}

	@Override
	public StructuredRepresentation representation() {
		if (isTop() || isBottom())
			return super.representation();

		StringBuilder builder = new StringBuilder();
		builder.append("IntervalRoundingTwoVariableLinearInequalityCartesian {\n");
		builder.append("  relational: ").append(left.representation()).append("\n");
		builder.append("  intervals: ").append(right.representation()).append("\n");
		builder.append("}");
		return new StringRepresentation(builder.toString());
	}
}
