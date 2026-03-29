error id: file:///C:/Users/DELL/OneDrive/Bureau/sorbonne/M2/S2/TAS/lisa-tutorial/src/main/java/it/unive/lisa/tutorial/TwoVariableLinearInequality.java:it/unive/lisa/analysis/relational/value/BaseRelationalValueDomain#
file:///C:/Users/DELL/OneDrive/Bureau/sorbonne/M2/S2/TAS/lisa-tutorial/src/main/java/it/unive/lisa/tutorial/TwoVariableLinearInequality.java
empty definition using pc, found symbol in pc: it/unive/lisa/analysis/relational/value/BaseRelationalValueDomain#
empty definition using semanticdb
empty definition using fallback
non-local guesses:

offset: 193
uri: file:///C:/Users/DELL/OneDrive/Bureau/sorbonne/M2/S2/TAS/lisa-tutorial/src/main/java/it/unive/lisa/tutorial/TwoVariableLinearInequality.java
text:
```scala



package it.unive.lisa.tutorial;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.relational.value.BaseRelationalVa@@lueDomain;
class TwoVariableLinearInequality implements BaseRelationalValueDomain<TwoVariableLinearInequality> {
    private final int a, b, c;
    private final boolean isBottom, isTop;
    private static final TwoVariableLinearInequality top, bottom;

    static {
        top = new TwoVariableLinearInequality(true);
        bottom = new TwoVariableLinearInequality(false);
    }

    public TwoVariableLinearInequality(int a, int b, int c) {
        this.a = a;
        this.b = b;
        this.c = c;
        this.isBottom = false;
        this.isTop = false;
    }

    private TwoVariableLinearInequality(boolean isTop) {
        this.a = 0;
        this.b = 0;
        this.c = 0;
        if(isTop) {
            this.isBottom = false;
            this.isTop = true;
        }
        else {
            this.isBottom = true;
            this.isTop = false;
        }
    }

    @Override
    public TwoVariableLinearInequality lubAux(TwoVariableLinearInequality other) throws SemanticException {
        if(this.isTop() || other.isTop())
            return top();
        if(this.isBottom)
            return other;
        if(other.isBottom)
            return this;
        if(this.equals(other))
            return this;
        return top();
    }

    @Override
    public boolean lessOrEqualAux(TwoVariableLinearInequality other) throws SemanticException {
        if(other.isTop)
            return true;
        if(other.isBottom)
            return this.isBottom;
        if(this.isTop)
            return false;
        if(this.isBottom)
            return true;
        return this.equals(other);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TwoVariableLinearInequality that)) return false;
        return a == that.a && b == that.b && c == that.c && isBottom == that.isBottom && isTop == that.isTop;
    }
  
}

```


#### Short summary: 

empty definition using pc, found symbol in pc: it/unive/lisa/analysis/relational/value/BaseRelationalValueDomain#