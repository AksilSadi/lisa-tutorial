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
		TwoVariableLinearInequality cleaned = cleanupIdentifier(id);

		if (expression instanceof Identifier) {
			Identifier other = (Identifier) expression;
			return cleaned.addEqualityConstraint(id, other, 0);
		}

		if (expression instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) expression;
			if (binary.getLeft() instanceof Identifier && binary.getRight() instanceof Constant) {
				Identifier other = (Identifier) binary.getLeft();
				Object value = ((Constant) binary.getRight()).getValue();
				if (value instanceof Integer) {
					int constant = (Integer) value;
					if (binary.getOperator() instanceof AdditionOperator)
						return cleaned.addEqualityConstraint(id, other, constant);
					if (binary.getOperator() instanceof SubtractionOperator)
						return cleaned.addEqualityConstraint(id, other, -constant);
				}
			}
		}

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
		if (expression instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) expression;
			if (binary.getLeft() instanceof Identifier && binary.getRight() instanceof Identifier) {
				Identifier left = (Identifier) binary.getLeft();
				Identifier right = (Identifier) binary.getRight();

				if (binary.getOperator() instanceof ComparisonLe)
					return addConstraint(left, right, 0);
				if (binary.getOperator() instanceof ComparisonLt)
					return addConstraint(left, right, -1);
				if (binary.getOperator() instanceof ComparisonGe)
					return addConstraint(right, left, 0);
				if (binary.getOperator() instanceof ComparisonGt)
					return addConstraint(right, left, -1);
				if (binary.getOperator() instanceof ComparisonEq)
					return addConstraint(left, right, 0).addConstraint(right, left, 0);
			}
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
		if (expression instanceof BinaryExpression) {
			BinaryExpression binary = (BinaryExpression) expression;
			if (binary.getLeft() instanceof Identifier && binary.getRight() instanceof Identifier) {
				Identifier left = (Identifier) binary.getLeft();
				Identifier right = (Identifier) binary.getRight();

				if (binary.getOperator() instanceof ComparisonLe)
					return satisfiesConstraint(left, right, 0);
				if (binary.getOperator() instanceof ComparisonLt)
					return satisfiesConstraint(left, right, -1);
				if (binary.getOperator() instanceof ComparisonGe)
					return satisfiesConstraint(right, left, 0);
				if (binary.getOperator() instanceof ComparisonGt)
					return satisfiesConstraint(right, left, -1);
				if (binary.getOperator() instanceof ComparisonEq)
					return satisfiesConstraint(left, right, 0).glb(satisfiesConstraint(right, left, 0));
			}
		}

		return Satisfiability.UNKNOWN;
	}

	@Override
	public TwoVariableLinearInequality pushScope(
			ScopeToken token)
			throws SemanticException {
		return this;
	}

	@Override
	public TwoVariableLinearInequality popScope(
			ScopeToken token)
			throws SemanticException {
		return this;
	}

	@Override
	public StructuredRepresentation representation() {
		return new StringRepresentation(toString());
	}

	private TwoVariableLinearInequality addConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		if (conflictsWithKnownConstraint(left, right, constant))
			return bottom();

		Constraint constraint = new Constraint(left, right, 1, -1, constant);
		ConstraintSet singleton = new ConstraintSet(Collections.singleton(constraint));
		return putState(left, getState(left).glb(singleton))
				.putState(right, getState(right).glb(singleton));
	}

	private TwoVariableLinearInequality addEqualityConstraint(
			Identifier left,
			Identifier right,
			int offset) {
		return addConstraint(left, right, offset)
				.addConstraint(right, left, -offset);
	}

	private Satisfiability satisfiesConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		for (Constraint known : getState(left).elements)
			if (known.left.equals(left)
					&& known.right.equals(right)
					&& known.leftCoeff == 1
					&& known.rightCoeff == -1
					&& known.constant <= constant)
				return Satisfiability.SATISFIED;

		if (conflictsWithKnownConstraint(left, right, constant))
			return Satisfiability.NOT_SATISFIED;

		return Satisfiability.UNKNOWN;
	}

	private boolean conflictsWithKnownConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		for (Constraint known : getState(left).elements)
			if (known.left.equals(right)
					&& known.right.equals(left)
					&& known.leftCoeff == 1
					&& known.rightCoeff == -1
					&& constant + known.constant < 0)
				return true;

		for (Constraint known : getState(right).elements)
			if (known.left.equals(right)
					&& known.right.equals(left)
					&& known.leftCoeff == 1
					&& known.rightCoeff == -1
					&& constant + known.constant < 0)
				return true;

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
