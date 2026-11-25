import QuantumNLS.FullWickH2

/-! FullWickH3 (haiku_inventory, R-140AE34B `thm:full-wick`, Stage 2, next step 1).

Completes the ℓ² identification of eq:full-norm-limit (wick_calculus.tex, the clause
`max_{z∈ℂ^I, ‖z‖≤1} |f(z)| = ‖f‖_{C(X)}`, with X the closed unit ball of the one-particle space):

  upper half (this file): for every ξ in the ℓ² unit ball of `ℤ → ℂ`,
      ‖f(ξ)‖ ≤ max_{z∈ℂ^I, ‖z‖≤1} |f(z)|.
  attained half (FullWickH2.l2_attains_unitBallSup): some ξ in the ℓ² unit ball attains it.

Together they say the classical maximum over the finite-coordinate ball equals the maximum of
|f| over the unit ball of ℓ²(ℤ). Proof: restrict ξ to I; the restriction has Euclidean norm at most
‖ξ‖ (a finite partial sum of ‖ξ a‖² is at most the full sum, the ℓ² norm identity); the restriction
agrees with ξ on I, so evalSym depends only on it (CoherentLowerBound.evalSym_congr); then the
continuous unit-ball bound SpectralUpperBound.le_unitBallSup applies.

Only the standard axioms (propext, Classical.choice, Quot.sound) occur; see the #print audit at the end.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH3

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds
open QuantumNLS.WickSpectralBridge QuantumNLS.OccupationHilbert
open QuantumNLS.FullWickH2

/-- The ℓ² norm squared as a sum of coordinate squares. -/
lemma norm_sq_tsum_one (ξ : QuantumNLS.OccupationUnitary.OneParticle) :
    ‖ξ‖ ^ 2 = ∑' n, ‖ξ n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ξ
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

/-- Square-summability of the coordinates of a one-particle vector. -/
lemma summable_sq_one (ξ : QuantumNLS.OccupationUnitary.OneParticle) :
    Summable (fun n => ‖ξ n‖ ^ 2) := by
  have h := (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

/-- Finite partial sums of the squared coordinates are bounded by the squared ℓ² norm. -/
lemma partial_sum_sq_le (ξ : QuantumNLS.OccupationUnitary.OneParticle) (I : Finset ℤ) :
    ∑ n ∈ I, ‖ξ n‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  rw [norm_sq_tsum_one ξ]
  exact (summable_sq_one ξ).sum_le_tsum I (fun n _ => by positivity)

/-- The finite-coordinate restriction of a one-particle vector to `ℂ^I`. -/
def restrictE (I : Finset ℤ) (ξ : QuantumNLS.OccupationUnitary.OneParticle) :
    EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun a : I => (ξ : ℤ → ℂ) (a : ℤ))

/-- The restriction has Euclidean norm at most that of `ξ`. -/
lemma restrictE_norm_sq (I : Finset ℤ) (ξ : QuantumNLS.OccupationUnitary.OneParticle) :
    ‖restrictE I ξ‖ ^ 2 = ∑ a ∈ I, ‖(ξ : ℤ → ℂ) a‖ ^ 2 := by
  have h1 : ‖restrictE I ξ‖ ^ 2 = ∑ a : I, ‖(ξ : ℤ → ℂ) (a : ℤ)‖ ^ 2 :=
    (EuclideanSpace.norm_sq_eq _).trans rfl
  rw [h1]
  exact Finset.sum_coe_sort I (fun a : ℤ => ‖(ξ : ℤ → ℂ) a‖ ^ 2)

/-- **ℓ² restriction bound**: `‖ξ‖ ≤ 1` implies `‖restrictE I ξ‖ ≤ 1`. -/
lemma restrictE_norm_le (I : Finset ℤ) {ξ : QuantumNLS.OccupationUnitary.OneParticle}
    (hξ : ‖ξ‖ ≤ 1) : ‖restrictE I ξ‖ ≤ 1 := by
  have hpart : ∑ a ∈ I, ‖(ξ : ℤ → ℂ) a‖ ^ 2 ≤ ‖ξ‖ ^ 2 := partial_sum_sq_le ξ I
  have hsq : ‖ξ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ξ]
  have hr : ‖restrictE I ξ‖ ^ 2 ≤ 1 := by
    rw [restrictE_norm_sq]
    linarith
  nlinarith [norm_nonneg (restrictE I ξ)]

/-- The restriction agrees with `ξ` on the label set, after the zero extension `zext`. -/
lemma restrictE_zext_agree (I : Finset ℤ) (ξ : QuantumNLS.OccupationUnitary.OneParticle) :
    ∀ a ∈ I, (ξ : ℤ → ℂ) a = zext I (restrictE I ξ) a := by
  intro a ha
  simp only [zext, dif_pos ha]
  rfl

/-- **Upper half of the ℓ² identification** (eq:full-norm-limit, `‖f‖_{C(X)}` clause): every
vector of the ℓ² unit ball of `ℤ → ℂ` has classical symbol bounded by the finite-coordinate
unit-ball maximum. -/
theorem l2_le_unitBallSup (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f)
    (ξ : QuantumNLS.OccupationUnitary.OneParticle) (hξ : ‖ξ‖ ≤ 1) :
    ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f) := by
  rw [CoherentLowerBound.evalSym_congr I hI (restrictE_zext_agree I ξ)]
  exact SpectralUpperBound.le_unitBallSup I (fun z => evalSym (zext I z) f)
    (continuous_evalSym_zext I hb hI) (restrictE I ξ) (restrictE_norm_le I hξ)

/-- **Two-sided identification** (eq:full-norm-limit, `= ‖f‖_{C(X)}` clause): the finite-coordinate
unit-ball maximum equals the supremum of `‖f(ξ)‖` over the ℓ² unit ball, and the supremum is attained. -/
theorem unitBallSup_eq_l2_max (I : Finset ℤ) {f : Sym} (hb : Balanced f) (hI : LabelsIn I f) :
    (∀ ξ : QuantumNLS.OccupationUnitary.OneParticle, ‖ξ‖ ≤ 1 →
        ‖evalSym (ξ : ℤ → ℂ) f‖ ≤ SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f))
    ∧ (∃ ξ : QuantumNLS.OccupationUnitary.OneParticle, ‖ξ‖ ≤ 1 ∧
        ‖evalSym (ξ : ℤ → ℂ) f‖ = SpectralUpperBound.unitBallSup I (fun z => evalSym (zext I z) f)) :=
  ⟨fun ξ hξ => l2_le_unitBallSup I hb hI ξ hξ, l2_attains_unitBallSup I hb hI⟩

end QuantumNLS.FullWickH3

#print axioms QuantumNLS.FullWickH3.norm_sq_tsum_one
#print axioms QuantumNLS.FullWickH3.summable_sq_one
#print axioms QuantumNLS.FullWickH3.partial_sum_sq_le
#print axioms QuantumNLS.FullWickH3.restrictE_norm_sq
#print axioms QuantumNLS.FullWickH3.restrictE_norm_le
#print axioms QuantumNLS.FullWickH3.restrictE_zext_agree
#print axioms QuantumNLS.FullWickH3.l2_le_unitBallSup
#print axioms QuantumNLS.FullWickH3.unitBallSup_eq_l2_max
