import QuantumNLS.FullWickH1
import QuantumNLS.PhysicalWickLimit

/-! FullWickH2 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 2: the norm limit).

Printed item (wick_calculus.tex, eq:full-norm-limit):
  for fixed f and every finite I containing its labels,
    lim_N ‖W_N^q(f)‖ = max_{z ∈ ℂ^I, ‖z‖ ≤ 1} |f(z)|.
This file proves the limit for the DEF-032 Bethe-chart operator `quantization (b N) (G N) f` for an
ARBITRARY family of Bethe bases `b N` and gauges `G N` (the selected full gauge is one instance).
The gauge and the Bethe basis enter only through the linear isometric equivalence
`J_N = occupationCoefficient (gaugedBasis (b N) (G N))`, so the norm equals the ungauged
auxiliary norm `‖WHil N f‖` for `N ≥ 1` (FullWickH1.quantization_norm_eq). The limit of that norm is
`CoherentLowerBound.wick_balanced_norm_limit` (supplied unit phases) specialised to the constant phase
`1` through `PhysicalWickLimit.WHilq_one`. No EXT-025 contract and no unaccepted predecessor is used.

The ℓ² identification of the classical maximum over ℂ^I with the sup over the unit ball of the
one-particle space (the `‖f‖_{C(X)}` clause of eq:full-norm-limit) is only PARTLY here: the attained
half `l2_attains_unitBallSup` is proved; the upper half (every ℓ² unit vector has |f| ≤ the ℂ^I
maximum) needs the restriction-norm lemma for `ℤ → ℂ` truncations, which is not yet written.

Only the standard axioms (propext, Classical.choice, Quot.sound) occur; see the #print audit at the end of the file.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH2

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds
open QuantumNLS.WickSpectralBridge QuantumNLS.OccupationHilbert
open QuantumNLS.BalancedWickDefinition QuantumNLS.BetheCoefficientTransform
open QuantumNLS.FullWickH1 Filter

variable {L : ℝ} [Fact (0 < L)]

/-- **Norm limit of the DEF-032 operator** (`eq:full-norm-limit`, unit-ball form) for any family of
Bethe bases and full-gauge phases. -/
theorem quantization_norm_limit (b : ∀ N : ℕ, BetheBasis L N)
    (G : ∀ N : ℕ, BetheOccupationGauge.Gauge) (I : Finset ℤ) {f : Sym} (hb : Balanced f)
    (hI : LabelsIn I f) :
    Tendsto (fun N => ‖quantization (b N) (G N) f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))) := by
  have h := CoherentLowerBound.wick_balanced_norm_limit
    (fun _ : ℕ => fun _ : QuantumNLS.Occupation.Occ => (1 : ℂ))
    (fun _ => show UnitGauge (fun _ : QuantumNLS.Occupation.Occ => (1 : ℂ)) from fun m => by simp)
    I hb hI
  have h1 : Tendsto (fun N => ‖WHil N f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))) := by
    refine h.congr (fun N => ?_)
    exact congrArg (fun T => ‖T‖) (PhysicalWickLimit.WHilq_one N _ f)
  have hEq : (fun N => ‖WHil N f‖) =ᶠ[atTop] (fun N => ‖quantization (b N) (G N) f‖) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (quantization_norm_eq (lt_of_lt_of_le Nat.zero_lt_one hN) (b N) (G N) f).symm
  exact h1.congr' hEq

/-- The labels of a `Polynomial` symbol are contained in its declared coordinate set. -/
lemma labelsIn_polynomial (f : BalancedWickDefinition.Polynomial) :
    LabelsIn f.coordinates f.symbol := by
  intro p hp a ha
  rcases ha with h | h
  · exact (f.labels p hp).1 (Finsupp.mem_support_iff.mpr h)
  · exact (f.labels p hp).2 (Finsupp.mem_support_iff.mpr h)

/-- **Norm limit for a balanced finite polynomial** (DEF-032 `wick`), on its coordinate set. -/
theorem wick_norm_limit_polynomial (b : ∀ N : ℕ, BetheBasis L N)
    (G : ∀ N : ℕ, BetheOccupationGauge.Gauge) (f : BalancedWickDefinition.Polynomial) :
    Tendsto (fun N => ‖wick (b N) (G N) f‖) atTop
      (nhds (SpectralUpperBound.unitBallSup f.coordinates
        (fun z => evalSym (zext f.coordinates z) f.symbol))) :=
  quantization_norm_limit b G f.coordinates f.balanced (labelsIn_polynomial f)


/-! ### The attained half of the ℓ² identification (`‖f‖_{C(X)}` clause) -/

/-- The classical symbol restricted to a finite label set is continuous on the ball `ℂ^I`
(balanced polynomial symbol written in finitely many words, `balanced_eq_polySym_I`). -/
lemma continuous_evalSym_zext (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    Continuous (fun z : EuclideanSpace ℂ I => evalSym (zext I z) f) := by
  have hF : (fun z : EuclideanSpace ℂ I => evalSym (zext I z) f)
      = SpectralUpperBound.polynomialSymbol I f.coeff.support f.coeff (fun p => wordI I p) := by
    funext z
    conv_lhs => rw [balanced_eq_polySym_I I hb hI]
    exact evalSym_polySym I _ _ _ z
  rw [hF]
  exact SpectralUpperBound.continuous_polynomialSymbol I _ _ _

/-- The classical unit-ball maximum of `eq:full-norm-limit` is attained by a vector of the ℓ²
unit ball of `ℤ → ℂ`: some `ξ` with `‖ξ‖ ≤ 1` has `‖f(ξ)‖ = max_{‖z‖≤1, z∈ℂ^I} |f(z)|`. -/
theorem l2_attains_unitBallSup (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    ∃ ξ : QuantumNLS.OccupationUnitary.OneParticle, ‖ξ‖ ≤ 1 ∧
      ‖evalSym (ξ : ℤ → ℂ) f‖ = SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f) := by
  obtain ⟨z, hz, heq⟩ := SpectralUpperBound.unitBallSup_attained I
    (fun z => evalSym (zext I z) f) (continuous_evalSym_zext I hb hI)
  obtain ⟨ξ, _, hn, hagree⟩ := CoherentLowerBound.exists_unit_extension I z hz
  refine ⟨ξ, hn.le, ?_⟩
  rw [heq]
  congr 1
  exact CoherentLowerBound.evalSym_congr I hI hagree

end QuantumNLS.FullWickH2

#print axioms QuantumNLS.FullWickH2.quantization_norm_limit
#print axioms QuantumNLS.FullWickH2.labelsIn_polynomial
#print axioms QuantumNLS.FullWickH2.wick_norm_limit_polynomial
#print axioms QuantumNLS.FullWickH2.continuous_evalSym_zext
#print axioms QuantumNLS.FullWickH2.l2_attains_unitBallSup
