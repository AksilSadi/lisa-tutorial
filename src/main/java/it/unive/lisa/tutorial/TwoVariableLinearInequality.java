package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGe;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

public class TwoVariableLinearInequality
		extends FunctionalLattice<TwoVariableLinearInequality, Identifier, TwoVariableLinearInequality.ConstraintSet>
		implements ValueDomain<TwoVariableLinearInequality> {

	public TwoVariableLinearInequality() {
		super(new ConstraintSet(Collections.emptySet()).top());
	}

	public TwoVariableLinearInequality(
			ConstraintSet lattice,
			Map<Identifier, ConstraintSet> function) {
		super(lattice, function);
	}

	@Override
	public TwoVariableLinearInequality mk(
			ConstraintSet lattice,
			Map<Identifier, ConstraintSet> function) {
		return new TwoVariableLinearInequality(lattice, function);
	}

	@Override
	public ConstraintSet stateOfUnknown(
			Identifier key) {
		return lattice.top();
	}

	@Override
	public TwoVariableLinearInequality top() {
		return new TwoVariableLinearInequality(lattice.top(), null);
	}

	@Override
	public TwoVariableLinearInequality bottom() {
		return new TwoVariableLinearInequality(lattice.bottom(), null);
	}

	@Override
	public TwoVariableLinearInequality assign(
			Identifier id,
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		if (isBottom())
			return this;

		TwoVariableLinearInequality cleaned = cleanupIdentifier(id);
		AffineForm form = asAffineForm(expression);
		if (form != null && form.variable != null)
			return cleaned.addEqualityConstraint(id, 1, form.variable, form.coefficient, form.offset);

		return cleaned;
	}

	@Override
	public TwoVariableLinearInequality smallStepSemantics(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return this;
	}

	@Override
	public TwoVariableLinearInequality assume(
			ValueExpression expression,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle)
			throws SemanticException {
		if (isBottom())
			return this;

		if (expression instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) expression;
			AffineForm left = asAffineForm(binary.getLeft());
			AffineForm right = asAffineForm(binary.getRight());
			if (left != null && right != null)
				return assumeNormalizedComparison(left, right, binary);
		}

		return this;
	}

	@Override
	public boolean knowsIdentifier(
			Identifier id) {
		return getKeys().contains(id);
	}

	@Override
	public TwoVariableLinearInequality forgetIdentifier(
			Identifier id)
			throws SemanticException {
		return cleanupIdentifier(id);
	}

	@Override
	public TwoVariableLinearInequality forgetIdentifiersIf(
			Predicate<Identifier> test)
			throws SemanticException {
		if (function == null)
			return this;

		Map<Identifier, ConstraintSet> result = mkNewFunction(function, true);
		for (Map.Entry<Identifier, ConstraintSet> entry : function.entrySet()) {
			Set<Constraint> filtered = new HashSet<>();
			for (Constraint constraint : entry.getValue().elements)
				if (!test.test(constraint.left) && !test.test(constraint.right))
					filtered.add(constraint);

			if (test.test(entry.getKey()))
				result.remove(entry.getKey());
			else
				result.put(entry.getKey(), new ConstraintSet(filtered));
		}
		return mk(lattice, result);
	}

	@Override
	public Satisfiability satisfies(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		if (isBottom())
			return Satisfiability.BOTTOM;

		if (expression instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) expression;
			AffineForm left = asAffineForm(binary.getLeft());
			AffineForm right = asAffineForm(binary.getRight());
			if (left != null && right != null)
				return satisfiesNormalizedComparison(left, right, binary);
		}

		return Satisfiability.UNKNOWN;
	}

	@Override
	public TwoVariableLinearInequality pushScope(
			ScopeToken token)
			throws SemanticException {
		return remapIdentifiers(id -> (Identifier) id.pushScope(token));
	}

	@Override
	public TwoVariableLinearInequality popScope(
			ScopeToken token)
			throws SemanticException {
		return remapIdentifiers(id -> {
			Identifier popped = (Identifier) id.popScope(token);
			return popped == null ? id : popped;
		});
	}

	@Override
	public StructuredRepresentation representation() {
		return super.representation();
	}

	private TwoVariableLinearInequality addConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		return addConstraint(left, 1, right, -1, constant);
	}

	private TwoVariableLinearInequality addConstraint(
			Identifier left,
			int leftCoeff,
			Identifier right,
			int rightCoeff,
			int constant) {
		if (isBottom())
			return this;
		if (left.equals(right) && leftCoeff + rightCoeff == 0)
			return constant < 0 ? bottom() : this;

		if (conflictsWithKnownConstraint(left, leftCoeff, right, rightCoeff, constant))
			return bottom();

		Constraint constraint = new Constraint(left, right, leftCoeff, rightCoeff, constant);
		ConstraintSet singleton = new ConstraintSet(Collections.singleton(constraint));
		TwoVariableLinearInequality withLeft = putState(left, getState(left).glb(singleton));
		return left.equals(right) ? withLeft : withLeft.putState(right, getState(right).glb(singleton));
	}

	private TwoVariableLinearInequality addEqualityConstraint(
			Identifier left,
			int leftCoeff,
			Identifier right,
			int rightCoeff,
			int offset) {
		return addConstraint(left, leftCoeff, right, -rightCoeff, offset)
				.addConstraint(left, -leftCoeff, right, rightCoeff, -offset);
	}

	private TwoVariableLinearInequality addEqualityConstraint(
			Identifier left,
			Identifier right,
			int offset) {
		return addEqualityConstraint(left, 1, right, 1, offset);
	}

	private Satisfiability satisfiesConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		return satisfiesConstraint(left, 1, right, -1, constant);
	}

	private Satisfiability satisfiesConstraint(
			Identifier left,
			int leftCoeff,
			Identifier right,
			int rightCoeff,
			int constant) {
		if (left.equals(right) && leftCoeff + rightCoeff == 0)
			return constant >= 0 ? Satisfiability.SATISFIED : Satisfiability.NOT_SATISFIED;

		for (Constraint known : getState(left).elements) {
			AlignedCoefficients aligned = align(known, left, right);
			if (aligned == null)
				continue;

			if (aligned.leftCoeff == leftCoeff
					&& aligned.rightCoeff == rightCoeff
					&& known.constant <= constant)
				return Satisfiability.SATISFIED;
		}

		if (conflictsWithKnownConstraint(left, leftCoeff, right, rightCoeff, constant))
			return Satisfiability.NOT_SATISFIED;

		return Satisfiability.UNKNOWN;
	}

	private boolean conflictsWithKnownConstraint(
			Identifier left,
			int leftCoeff,
			Identifier right,
			int rightCoeff,
			int constant) {
		if (left.equals(right) && leftCoeff + rightCoeff == 0)
			return constant < 0;

		for (Constraint known : getState(left).elements) {
			AlignedCoefficients aligned = align(known, left, right);
			if (aligned != null
					&& aligned.leftCoeff == -leftCoeff
					&& aligned.rightCoeff == -rightCoeff
					&& constant + known.constant < 0)
				return true;
		}

		return false;
	}

	private TwoVariableLinearInequality cleanupIdentifier(
			Identifier id) {
		if (function == null)
			return this;

		Map<Identifier, ConstraintSet> result = mkNewFunction(function, true);
		for (Map.Entry<Identifier, ConstraintSet> entry : function.entrySet()) {
			Set<Constraint> filtered = new HashSet<>();
			for (Constraint constraint : entry.getValue().elements)
				if (!constraint.mentions(id))
					filtered.add(constraint);

			if (entry.getKey().equals(id))
				result.remove(id);
			else
				result.put(entry.getKey(), new ConstraintSet(filtered));
		}

		return mk(lattice, result);
	}

	private TwoVariableLinearInequality assumeNormalizedComparison(
			AffineForm left,
			AffineForm right,
			BinaryExpression binary) {
		NormalizedConstraint normalized = normalize(left, right);
		if (normalized == null)
			return evaluateConstantComparison(left.offset, right.offset, binary);

		if (binary.getOperator() instanceof ComparisonLe)
			return addConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant);
		if (binary.getOperator() instanceof ComparisonLt)
			return addConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant - 1);
		if (binary.getOperator() instanceof ComparisonGe)
			return addConstraint(normalized.left, -normalized.leftCoeff, normalized.right, -normalized.rightCoeff,
					-normalized.constant);
		if (binary.getOperator() instanceof ComparisonGt)
			return addConstraint(normalized.left, -normalized.leftCoeff, normalized.right, -normalized.rightCoeff,
					-normalized.constant - 1);
		if (binary.getOperator() instanceof ComparisonEq)
			return addConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant)
					.addConstraint(normalized.left, -normalized.leftCoeff, normalized.right,
							-normalized.rightCoeff, -normalized.constant);

		return this;
	}

	private Satisfiability satisfiesNormalizedComparison(
			AffineForm left,
			AffineForm right,
			BinaryExpression binary) {
		NormalizedConstraint normalized = normalize(left, right);
		if (normalized == null)
			return evaluateConstantComparisonSatisfiability(left.offset, right.offset, binary);

		if (binary.getOperator() instanceof ComparisonLe)
			return satisfiesConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant);
		if (binary.getOperator() instanceof ComparisonLt)
			return satisfiesConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant - 1);
		if (binary.getOperator() instanceof ComparisonGe)
			return satisfiesConstraint(normalized.left, -normalized.leftCoeff, normalized.right,
					-normalized.rightCoeff, -normalized.constant);
		if (binary.getOperator() instanceof ComparisonGt)
			return satisfiesConstraint(normalized.left, -normalized.leftCoeff, normalized.right,
					-normalized.rightCoeff, -normalized.constant - 1);
		if (binary.getOperator() instanceof ComparisonEq)
			return satisfiesConstraint(normalized.left, normalized.leftCoeff, normalized.right, normalized.rightCoeff,
					normalized.constant)
					.glb(satisfiesConstraint(normalized.left, -normalized.leftCoeff, normalized.right,
							-normalized.rightCoeff, -normalized.constant));

		return Satisfiability.UNKNOWN;
	}

	private AffineForm asAffineForm(
			ValueExpression expression) {
		if (expression instanceof Identifier)
			return new AffineForm((Identifier) expression, 1, 0);

		Integer constant = asIntegerConstant(expression);
		if (constant != null)
			return new AffineForm(null, 0, constant);

		if (!(expression instanceof BinaryExpression))
			return null;

		BinaryExpression binary = (BinaryExpression) expression;
		AffineForm left = asAffineForm(binary.getLeft());
		AffineForm right = asAffineForm(binary.getRight());
		if (left == null || right == null)
			return null;

		if (binary.getOperator() instanceof AdditionOperator) {
			if (left.variable != null && right.variable == null)
				return new AffineForm(left.variable, left.coefficient, left.offset + right.offset);
			if (left.variable == null && right.variable != null)
				return new AffineForm(right.variable, right.coefficient, left.offset + right.offset);
		}

		if (binary.getOperator() instanceof SubtractionOperator
				&& left.variable != null
				&& right.variable == null)
			return new AffineForm(left.variable, left.coefficient, left.offset - right.offset);

		if (binary.getOperator() instanceof MultiplicationOperator) {
			if (left.variable != null && right.variable == null)
				return new AffineForm(left.variable, left.coefficient * right.offset, left.offset * right.offset);
			if (left.variable == null && right.variable != null)
				return new AffineForm(right.variable, left.offset * right.coefficient, left.offset * right.offset);
		}

		return null;
	}

	private NormalizedConstraint normalize(
			AffineForm left,
			AffineForm right) {
		if (left.variable == null && right.variable == null)
			return null;

		if (left.variable != null && right.variable != null)
			return new NormalizedConstraint(left.variable, left.coefficient, right.variable, -right.coefficient,
					right.offset - left.offset);

		if (left.variable != null)
			return new NormalizedConstraint(left.variable, left.coefficient, left.variable, 0,
					right.offset - left.offset);

		return new NormalizedConstraint(right.variable, 0, right.variable, -right.coefficient,
				right.offset - left.offset);
	}

	private TwoVariableLinearInequality evaluateConstantComparison(
			int left,
			int right,
			BinaryExpression binary) {
		boolean satisfied = evaluateConstantComparisonBoolean(left, right, binary);
		return satisfied ? this : bottom();
	}

	private Satisfiability evaluateConstantComparisonSatisfiability(
			int left,
			int right,
			BinaryExpression binary) {
		return Satisfiability.fromBoolean(evaluateConstantComparisonBoolean(left, right, binary));
	}

	private boolean evaluateConstantComparisonBoolean(
			int left,
			int right,
			BinaryExpression binary) {
		if (binary.getOperator() instanceof ComparisonLe)
			return left <= right;
		if (binary.getOperator() instanceof ComparisonLt)
			return left < right;
		if (binary.getOperator() instanceof ComparisonGe)
			return left >= right;
		if (binary.getOperator() instanceof ComparisonGt)
			return left > right;
		if (binary.getOperator() instanceof ComparisonEq)
			return left == right;
		return false;
	}

	private Integer asIntegerConstant(
			ValueExpression expression) {
		if (!(expression instanceof Constant))
			return null;

		Object value = ((Constant) expression).getValue();
		return value instanceof Integer ? (Integer) value : null;
	}

	private TwoVariableLinearInequality remapIdentifiers(
			IdentifierMapper mapper)
			throws SemanticException {
		if (function == null)
			return this;

		Map<Identifier, ConstraintSet> result = mkNewFunction(null, false);
		for (Map.Entry<Identifier, ConstraintSet> entry : function.entrySet()) {
			Identifier mappedKey = mapper.apply(entry.getKey());
			ConstraintSet mappedState = remapConstraintSet(entry.getValue(), mapper);
			ConstraintSet previous = result.get(mappedKey);
			result.put(mappedKey, previous == null ? mappedState : previous.glb(mappedState));
		}

		return mk(lattice, result);
	}

	private ConstraintSet remapConstraintSet(
			ConstraintSet state,
			IdentifierMapper mapper)
			throws SemanticException {
		Set<Constraint> remapped = new HashSet<>();
		for (Constraint constraint : state.elements)
			remapped.add(new Constraint(
					mapper.apply(constraint.left),
					mapper.apply(constraint.right),
					constraint.leftCoeff,
					constraint.rightCoeff,
					constraint.constant));

		return new ConstraintSet(remapped, state.isTop());
	}

	@FunctionalInterface
	private interface IdentifierMapper {

		Identifier apply(
				Identifier id)
				throws SemanticException;
	}

	private static final class AffineForm {

		private final Identifier variable;
		private final int coefficient;
		private final int offset;

		private AffineForm(
				Identifier variable,
				int coefficient,
				int offset) {
			this.variable = variable;
			this.coefficient = coefficient;
			this.offset = offset;
		}
	}

	private static final class NormalizedConstraint {

		private final Identifier left;
		private final int leftCoeff;
		private final Identifier right;
		private final int rightCoeff;
		private final int constant;

		private NormalizedConstraint(
				Identifier left,
				int leftCoeff,
				Identifier right,
				int rightCoeff,
				int constant) {
			this.left = left;
			this.leftCoeff = leftCoeff;
			this.right = right;
			this.rightCoeff = rightCoeff;
			this.constant = constant;
		}
	}

	private static final class AlignedCoefficients {

		private final int leftCoeff;
		private final int rightCoeff;

		private AlignedCoefficients(
				int leftCoeff,
				int rightCoeff) {
			this.leftCoeff = leftCoeff;
			this.rightCoeff = rightCoeff;
		}
	}

	private AlignedCoefficients align(
			Constraint constraint,
			Identifier left,
			Identifier right) {
		if (constraint.left.equals(left) && constraint.right.equals(right))
			return new AlignedCoefficients(constraint.leftCoeff, constraint.rightCoeff);
		if (constraint.left.equals(right) && constraint.right.equals(left))
			return new AlignedCoefficients(constraint.rightCoeff, constraint.leftCoeff);
		return null;
	}

	public static class Constraint {

		public final Identifier left;
		public final Identifier right;
		public final int leftCoeff;
		public final int rightCoeff;
		public final int constant;

		public Constraint(
				Identifier left,
				Identifier right,
				int leftCoeff,
				int rightCoeff,
				int constant) {
			this.left = left;
			this.right = right;
			this.leftCoeff = leftCoeff;
			this.rightCoeff = rightCoeff;
			this.constant = constant;
		}

		public boolean mentions(
				Identifier id) {
			return left.equals(id) || right.equals(id);
		}

		@Override
		public boolean equals(
				Object obj) {
			if (this == obj)
				return true;
			if (!(obj instanceof Constraint))
				return false;
			Constraint other = (Constraint) obj;
			return leftCoeff == other.leftCoeff
					&& rightCoeff == other.rightCoeff
					&& constant == other.constant
					&& Objects.equals(left, other.left)
					&& Objects.equals(right, other.right);
		}

		@Override
		public int hashCode() {
			return Objects.hash(left, right, leftCoeff, rightCoeff, constant);
		}

		@Override
		public String toString() {
			return leftCoeff + "*" + left + " + " + rightCoeff + "*" + right + " <= " + constant;
		}
	}

	public static class ConstraintSet extends InverseSetLattice<ConstraintSet, Constraint> {

		public ConstraintSet(
				Set<Constraint> elements) {
			super(elements, elements.isEmpty());
		}

		public ConstraintSet(
				Set<Constraint> elements,
				boolean isTop) {
			super(elements, isTop);
		}

		@Override
		public ConstraintSet mk(
				Set<Constraint> set) {
			return new ConstraintSet(set);
		}

		@Override
		public ConstraintSet top() {
			return new ConstraintSet(Collections.emptySet(), true);
		}

		@Override
		public ConstraintSet bottom() {
			return new ConstraintSet(Collections.emptySet(), false);
		}

		@Override
		public ConstraintSet wideningAux(
				ConstraintSet other)
				throws SemanticException {
			return other.elements.containsAll(elements) ? other : top();
		}
	}
}
