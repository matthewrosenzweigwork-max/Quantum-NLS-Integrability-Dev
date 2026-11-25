import QuantumNLS.Ext025BMeasure

/-!
# GP-11 application for LOCAL-005 word sums

After coding the countable set of intermediate mode paths by naturals, the
absolute word terms form a nonnegative series.  GP-11 identifies that series
with the increasing supremum of its finite partial sums.  A separate LOCAL-001
bound is what makes that supremum finite.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace QuantumNLS.ResolventWordGP11LOCAL005

/-- Counting-measure monotone convergence for the nonnegative terms of a
coded resolvent-word majorant. -/
theorem nonnegativeWordTruncations (a : ℕ → ℝ≥0∞) :
    ∑' n, a n = ⨆ N, ∑ n ∈ Finset.range N, a n :=
  QuantumNLS.Ext025BMeasure.«FIN-EXT025-GP-11-counting» a

#print axioms nonnegativeWordTruncations

end QuantumNLS.ResolventWordGP11LOCAL005
