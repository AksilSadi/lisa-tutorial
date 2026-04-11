package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
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
import it.unive.lisa.util.representation.MapRepresentation;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.TreeMap;
import java.util.TreeSet;
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
	public boolean lessOrEqualAux(
			TwoVariableLinearInequality other)
			throws SemanticException {
		if (isBottom())
			return true;
		if (other.isTop())
			return true;
		if (isTop())
			return other.isTop();
		if (other.isBottom())
			return isBottom();

		Set<Constraint> thisClosed = closedConstraints();
		for (Constraint target : other.closedConstraints()) {
			boolean found = false;
			for (Constraint mine : thisClosed)
				if (mine.entails(target)) {
					found = true;
					break;
				}

			if (!found)
				return false;
		}

		return true;
	}

	@Override
	public TwoVariableLinearInequality assign(
			Identifier id,
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		if (isBottom() || isSpecialIdentifier(id))
			return this;

		TwoVariableLinearInequality cleaned = cleanupIdentifier(id);
		AffineForm form = asAffineForm(expression);
		if (form != null && form.variable != null && !isSpecialIdentifier(form.variable))
			return cleaned.addEqualityConstraint(id, 1, form.variable, form.coefficient, form.offset);
		if (form != null && form.variable == null)
			return cleaned.addConstantEquality(id, form.offset);

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
			if (left != null && right != null && !mentionsSpecialIdentifier(left, right))
				return assumeNormalizedComparison(left, right, binary);
		}

		return this;
	}

	@Override
	public boolean knowsIdentifier(
			Identifier id) {
		return !isSpecialIdentifier(id) && getKeys().contains(id);
	}

	@Override
	public TwoVariableLinearInequality forgetIdentifier(
			Identifier id)
			throws SemanticException {
		if (isSpecialIdentifier(id))
			return this;

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
				if ((constraint.left == null || !test.test(constraint.left))
						&& (constraint.right == null || !test.test(constraint.right)))
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
			if (left != null && right != null && !mentionsSpecialIdentifier(left, right))
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
		if (isTop())
			return Lattice.topRepresentation();
		if (isBottom())
			return Lattice.bottomRepresentation();

		TreeSet<Constraint> constraints = new TreeSet<>(Comparator.comparing(Constraint::toString));
		constraints.addAll(closedConstraints());

		Map<StructuredRepresentation, StructuredRepresentation> mapping = new HashMap<>();
		mapping.put(new StringRepresentation("constraints"),
				new StringRepresentation(constraints.toString()));

		for (Identifier id : sortedIdentifiers())
			mapping.put(new StringRepresentation(id), getState(id).representation());

		return new MapRepresentation(mapping);
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

		Constraint normalized = new Constraint(left, right, leftCoeff, rightCoeff, constant).normalize();
		if (normalized.isTrivial())
			return this;
		if (normalized.isUnsatisfiable())
			return bottom();
		if (conflictsWithKnownConstraint(normalized))
			return bottom();

		ConstraintSet singleton = new ConstraintSet(Collections.singleton(normalized));
		TwoVariableLinearInequality withLeft = putState(normalized.left,
				mergeConstraintSets(getState(normalized.left), singleton));
		if (normalized.right == null || normalized.left.equals(normalized.right))
			return withLeft;
		return withLeft.putState(normalized.right,
				mergeConstraintSets(withLeft.getState(normalized.right), singleton));
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

	private TwoVariableLinearInequality addConstantEquality(
			Identifier id,
			int constant) {
		return addConstraint(id, 1, null, 0, constant)
				.addConstraint(id, -1, null, 0, -constant);
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
		Constraint target = new Constraint(left, right, leftCoeff, rightCoeff, constant).normalize();
		if (target.isTrivial())
			return Satisfiability.SATISFIED;
		if (target.isUnsatisfiable())
			return Satisfiability.NOT_SATISFIED;
		if (containsEntailingConstraint(target))
			return Satisfiability.SATISFIED;
		if (containsEntailingConstraint(target.negate()))
			return Satisfiability.NOT_SATISFIED;

		return Satisfiability.UNKNOWN;
	}

	private boolean conflictsWithKnownConstraint(
			Constraint candidate) {
		return containsEntailingConstraint(candidate.negate());
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
			SymbolicExpression expression) {
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
			return new NormalizedConstraint(left.variable, left.coefficient, null, 0,
					right.offset - left.offset);

		return new NormalizedConstraint(right.variable, -right.coefficient, null, 0,
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
			SymbolicExpression expression) {
		if (!(expression instanceof Constant))
			return null;

		Object value = ((Constant) expression).getValue();
		return value instanceof Integer ? (Integer) value : null;
	}

	private Set<Constraint> allConstraints() {
		Set<Constraint> constraints = new HashSet<>();
		if (function == null)
			return constraints;

		for (ConstraintSet state : function.values())
			constraints.addAll(state.elements);

		return constraints;
	}

	private ConstraintSet mergeConstraintSets(
			ConstraintSet left,
			ConstraintSet right) {
		Set<Constraint> merged = new HashSet<>(left.elements);
		merged.addAll(right.elements);
		return new ConstraintSet(merged);
	}

	private Set<Constraint> closedConstraints() {
		return computeClosure(allConstraints());
	}

	private Set<Identifier> sortedIdentifiers() {
		TreeSet<Identifier> sorted = new TreeSet<>((left, right) -> {
			int cmp = left.toString().compareTo(right.toString());
			if (cmp != 0)
				return cmp;
			return left.getClass().getName().compareTo(right.getClass().getName());
		});
		sorted.addAll(getKeys());
		return sorted;
	}

	private boolean mentionsSpecialIdentifier(
			AffineForm left,
			AffineForm right) {
		return left.variable != null && isSpecialIdentifier(left.variable)
				|| right.variable != null && isSpecialIdentifier(right.variable);
	}

	private boolean isSpecialIdentifier(
			Identifier id) {
		String name = id.getName();
		return name.contains("heap")
				|| name.contains("this")
				|| name.startsWith("&pp@");
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
					constraint.left == null ? null : mapper.apply(constraint.left),
					constraint.right == null ? null : mapper.apply(constraint.right),
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

	private boolean containsEntailingConstraint(
			Constraint target) {
		for (Constraint known : closedConstraints())
			if (known.entails(target))
				return true;
		return false;
	}

	private Set<Constraint> computeClosure(
			Set<Constraint> constraints) {
		Set<Constraint> current = sanitizeConstraints(constraints);
		while (true) {
			if (containsUnsatisfiableConstraint(current))
				return current;

			Set<Constraint> next = new HashSet<>(current);
			next.addAll(deriveConsequences(current));
			next = sanitizeConstraints(next);

			if (next.equals(current))
				return next;
			current = next;
		}
	}

	private Set<Constraint> deriveConsequences(
			Set<Constraint> constraints) {
		Set<Constraint> generated = new HashSet<>();
		for (Constraint first : constraints)
			for (Constraint second : constraints) {
				if (first.equals(second))
					continue;

				Set<Identifier> common = new HashSet<>(first.variables());
				common.retainAll(second.variables());
				for (Identifier pivot : common) {
					Constraint derived = eliminateSharedVariable(first, second, pivot);
					if (derived != null)
						generated.add(derived.normalize());
				}
			}

		return sanitizeConstraints(generated);
	}

	private Constraint eliminateSharedVariable(
			Constraint first,
			Constraint second,
			Identifier pivot) {
		int firstPivotCoeff = first.coefficientOf(pivot);
		int secondPivotCoeff = second.coefficientOf(pivot);
		if (firstPivotCoeff == 0 || secondPivotCoeff == 0 || firstPivotCoeff * secondPivotCoeff >= 0)
			return null;

		int firstScale = Math.abs(secondPivotCoeff);
		int secondScale = Math.abs(firstPivotCoeff);
		int constant = firstScale * first.constant + secondScale * second.constant;

		Map<Identifier, Integer> coefficients = new HashMap<>();
		accumulateCoefficient(coefficients, first.left, firstScale * first.leftCoeff, pivot);
		accumulateCoefficient(coefficients, first.right, firstScale * first.rightCoeff, pivot);
		accumulateCoefficient(coefficients, second.left, secondScale * second.leftCoeff, pivot);
		accumulateCoefficient(coefficients, second.right, secondScale * second.rightCoeff, pivot);
		coefficients.entrySet().removeIf(entry -> entry.getValue() == 0);

		Iterator<Map.Entry<Identifier, Integer>> iterator = coefficients.entrySet().iterator();
		Identifier left = null;
		Identifier right = null;
		int leftCoeff = 0;
		int rightCoeff = 0;

		if (iterator.hasNext()) {
			Map.Entry<Identifier, Integer> entry = iterator.next();
			left = entry.getKey();
			leftCoeff = entry.getValue();
		}

		if (iterator.hasNext()) {
			Map.Entry<Identifier, Integer> entry = iterator.next();
			right = entry.getKey();
			rightCoeff = entry.getValue();
		}

		return new Constraint(left, right, leftCoeff, rightCoeff, constant).normalize();
	}

	private void accumulateCoefficient(
			Map<Identifier, Integer> coefficients,
			Identifier id,
			int value,
			Identifier pivot) {
		if (id == null || value == 0 || id.equals(pivot))
			return;
		coefficients.merge(id, value, Integer::sum);
	}

	private Set<Constraint> sanitizeConstraints(
			Set<Constraint> constraints) {
		if (constraints.isEmpty())
			return constraints;

		Set<Constraint> cleaned = removeTrivialConstraints(constraints);
		if (containsUnsatisfiableConstraint(cleaned))
			return Collections.singleton(new Constraint(null, null, 0, 0, -1));
		return tightenConstraints(cleaned);
	}

	private Set<Constraint> removeTrivialConstraints(
			Set<Constraint> constraints) {
		Set<Constraint> cleaned = new HashSet<>();
		for (Constraint constraint : constraints)
			if (!constraint.isTrivial())
				cleaned.add(constraint);
		return cleaned;
	}

	private Set<Constraint> tightenConstraints(
			Set<Constraint> constraints) {
		Set<Constraint> tightened = new HashSet<>();
		for (Constraint current : constraints) {
			boolean shouldAdd = true;
			Set<Constraint> toRemove = new HashSet<>();
			for (Constraint existing : tightened)
				if (current.sameLeftPart(existing)) {
					if (current.constant <= existing.constant)
						toRemove.add(existing);
					else
						shouldAdd = false;
				}

			tightened.removeAll(toRemove);
			if (shouldAdd)
				tightened.add(current);
		}
		return tightened;
	}

	private boolean containsUnsatisfiableConstraint(
			Set<Constraint> constraints) {
		for (Constraint constraint : constraints)
			if (constraint.isUnsatisfiable())
				return true;
		return false;
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
			return left != null && left.equals(id) || right != null && right.equals(id);
		}

		public boolean isTrivial() {
			return leftCoeff == 0 && rightCoeff == 0 && constant >= 0;
		}

		public boolean isUnsatisfiable() {
			return leftCoeff == 0 && rightCoeff == 0 && constant < 0;
		}

		public boolean sameLeftPart(
				Constraint other) {
			return leftCoeff == other.leftCoeff
					&& rightCoeff == other.rightCoeff
					&& Objects.equals(left, other.left)
					&& Objects.equals(right, other.right);
		}

		public boolean entails(
				Constraint other) {
			return sameLeftPart(other) && constant <= other.constant;
		}

		public Set<Identifier> variables() {
			Set<Identifier> variables = new HashSet<>();
			if (left != null && leftCoeff != 0)
				variables.add(left);
			if (right != null && rightCoeff != 0)
				variables.add(right);
			return variables;
		}

		public int coefficientOf(
				Identifier id) {
			int coefficient = 0;
			if (left != null && left.equals(id))
				coefficient += leftCoeff;
			if (right != null && right.equals(id))
				coefficient += rightCoeff;
			return coefficient;
		}

		public Constraint normalize() {
			Map<Identifier, Integer> coefficients = new TreeMap<>(Comparator.comparing(Identifier::getName));
			if (left != null && leftCoeff != 0)
				coefficients.merge(left, leftCoeff, Integer::sum);
			if (right != null && rightCoeff != 0)
				coefficients.merge(right, rightCoeff, Integer::sum);
			coefficients.entrySet().removeIf(entry -> entry.getValue() == 0);

			Iterator<Map.Entry<Identifier, Integer>> iterator = coefficients.entrySet().iterator();
			Identifier normalizedLeft = null;
			Identifier normalizedRight = null;
			int normalizedLeftCoeff = 0;
			int normalizedRightCoeff = 0;
			if (iterator.hasNext()) {
				Map.Entry<Identifier, Integer> entry = iterator.next();
				normalizedLeft = entry.getKey();
				normalizedLeftCoeff = entry.getValue();
			}
			if (iterator.hasNext()) {
				Map.Entry<Identifier, Integer> entry = iterator.next();
				normalizedRight = entry.getKey();
				normalizedRightCoeff = entry.getValue();
			}

			int divisor = gcd(gcd(normalizedLeftCoeff, normalizedRightCoeff), constant);
			if (divisor != 0) {
				normalizedLeftCoeff /= divisor;
				normalizedRightCoeff /= divisor;
			}
			int normalizedConstant = divisor == 0 ? constant : constant / divisor;

			return new Constraint(normalizedLeft, normalizedRight, normalizedLeftCoeff, normalizedRightCoeff,
					normalizedConstant);
		}

		public Constraint negate() {
			return new Constraint(left, right, -leftCoeff, -rightCoeff, -constant - 1).normalize();
		}

		private int gcd(
				int left,
				int right) {
			left = Math.abs(left);
			right = Math.abs(right);
			while (right != 0) {
				int tmp = left % right;
				left = right;
				right = tmp;
			}
			return left == 0 ? 1 : left;
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
			StringBuilder builder = new StringBuilder();
			boolean written = false;
			if (left != null && leftCoeff != 0) {
				builder.append(leftCoeff).append("*").append(left);
				written = true;
			}
			if (right != null && rightCoeff != 0) {
				if (written && rightCoeff > 0)
					builder.append(" + ");
				else if (written)
					builder.append(" ");
				builder.append(rightCoeff).append("*").append(right);
				written = true;
			}
			if (!written)
				builder.append("0");
			return builder.append(" <= ").append(constant).toString();
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
