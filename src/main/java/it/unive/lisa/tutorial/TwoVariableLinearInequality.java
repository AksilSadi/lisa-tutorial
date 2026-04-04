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
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGe;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonGt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;

import java.util.Collections;
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
		return this;
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
		if (function == null || !function.containsKey(id))
			return this;

		Map<Identifier, ConstraintSet> result = mkNewFunction(function, true);
		result.remove(id);
		return mk(lattice, result);
	}

	@Override
	public TwoVariableLinearInequality forgetIdentifiersIf(
			Predicate<Identifier> test)
			throws SemanticException {
		if (function == null)
			return this;

		Map<Identifier, ConstraintSet> result = mkNewFunction(function, true);
		result.keySet().removeIf(test);
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

	private TwoVariableLinearInequality addConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		Constraint constraint = new Constraint(left, right, 1, -1, constant);
		ConstraintSet singleton = new ConstraintSet(Collections.singleton(constraint));
		return putState(left, getState(left).glb(singleton))
				.putState(right, getState(right).glb(singleton));
	}

	private Satisfiability satisfiesConstraint(
			Identifier left,
			Identifier right,
			int constant) {
		Constraint constraint = new Constraint(left, right, 1, -1, constant);
		if (getState(left).contains(constraint) && getState(right).contains(constraint))
			return Satisfiability.SATISFIED;
		return Satisfiability.UNKNOWN;
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
