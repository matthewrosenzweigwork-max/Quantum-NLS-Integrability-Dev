import NlsGge.Hierarchy.RiccatiActualMonomialTopSlotSplitIntegralRecovery31First
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- A finite index for every occurrence of every jet variable in a source
monomial. The `Fin (q v)` coordinate retains repeated factors. -/
def riccatiActualMonomialSlotFinsetRecovery31Fourth
    (q : Jet →₀ ℕ) : Finset (Σ v : Jet, Fin (q v)) :=
  q.support.sigma (fun v => Finset.univ)

/-- The finite slot family has the same cardinality as the total monomial
factor count, including exponents. -/
theorem riccatiActualMonomialSlotFinset_cardRecovery31Fourth
    (q : Jet →₀ ℕ) :
    (riccatiActualMonomialSlotFinsetRecovery31Fourth q).card = q.degree := by
  classical
  rw [riccatiActualMonomialSlotFinsetRecovery31Fourth, Finset.card_sigma,
    Finsupp.degree_apply]
  simp [Finsupp.sum, Finset.card_fin]

/-- Multiplying one value for each finite slot recovers the Finsupp power
product for the original monomial. -/
theorem riccatiActualMonomialSlotFinset_prodRecovery31Fourth
    (q : Jet →₀ ℕ) (f : Jet → ℂ) :
    (∏ s ∈ riccatiActualMonomialSlotFinsetRecovery31Fourth q, f s.1) =
      q.prod (fun v n => f v ^ n) := by
  classical
  rw [riccatiActualMonomialSlotFinsetRecovery31Fourth, Finset.prod_sigma]
  simp [Finsupp.prod, Finset.prod_const, Finset.card_fin]

/-- The finite slots selected by the top-order predicate multiply to the
Finsupp product of the top-filtered exponent. -/
theorem riccatiActualMonomialSlotFinset_topProd_eq_filterRecovery31Fourth
    (m : ℕ) (q : Jet →₀ ℕ) (f : Jet → ℂ) :
    (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => s.1.2 + 1 = m), f s.1) =
        (q.filter (fun v : Jet => v.2 + 1 = m)).prod (fun v n => f v ^ n) := by
  classical
  rw [riccatiActualMonomialSlotFinsetRecovery31Fourth, Finset.filter_sigma,
    Finset.prod_sigma]
  simp only [Finset.prod_const]
  simp only [Finsupp.prod, Finsupp.support_filter, Finsupp.filter_apply]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hp : v.2 + 1 = m <;> simp [hp, Finset.card_fin]

/-- The complementary finite slots multiply to the complementary filtered
Finsupp product. -/
theorem riccatiActualMonomialSlotFinset_lowerProd_eq_filterRecovery31Fourth
    (m : ℕ) (q : Jet →₀ ℕ) (f : Jet → ℂ) :
    (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => ¬ s.1.2 + 1 = m), f s.1) =
        (q.filter (fun v : Jet => ¬ v.2 + 1 = m)).prod (fun v n => f v ^ n) := by
  classical
  rw [riccatiActualMonomialSlotFinsetRecovery31Fourth, Finset.filter_sigma,
    Finset.prod_sigma]
  simp only [Finset.prod_const]
  simp only [Finsupp.prod, Finsupp.support_filter, Finsupp.filter_apply]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hp : ¬ v.2 + 1 = m <;> simp [hp, Finset.card_fin]

/-- The finite slot product separates into actual top-order slots and all
lower-order slots, with the top predicate exactly matching the checked
source multiplicity convention. -/
theorem riccatiActualMonomialSlotFinset_topSplitRecovery31Fourth
    (m : ℕ) (q : Jet →₀ ℕ) (f : Jet → ℂ) :
    (∏ s ∈ riccatiActualMonomialSlotFinsetRecovery31Fourth q, f s.1) =
      (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
        (fun s => s.1.2 + 1 = m), f s.1) *
      (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
        (fun s => ¬ s.1.2 + 1 = m), f s.1) := by
  classical
  exact (Finset.prod_filter_mul_prod_filter_not
    (riccatiActualMonomialSlotFinsetRecovery31Fourth q)
    (fun s => s.1.2 + 1 = m) (fun s => f s.1)).symm

/-- The number of finite top-order slots is exactly the multiplicity sum
bounded by the actual derivative-count theorem. -/
theorem riccatiActualMonomialSlotFinset_topCardRecovery31Fourth
    (m : ℕ) (q : Jet →₀ ℕ) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => s.1.2 + 1 = m)).card =
      riccatiTopJetSlotMultiplicityMinimumRecovery30Third m q := by
  classical
  rw [riccatiActualMonomialSlotFinsetRecovery31Fourth, Finset.filter_sigma,
    Finset.card_sigma]
  unfold riccatiTopJetSlotMultiplicityMinimumRecovery30Third
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : v.2 + 1 = m <;> simp [hp, Finset.card_fin]

/-- The actual derivative-count premise leaves no more than two occurrences
of order `m-1` in the finite slot family. -/
theorem riccatiActualMonomialSlotFinset_topCard_le_twoRecovery31Fourth
    (m : ℕ) (hm : 2 ≤ m) (q : Jet →₀ ℕ)
    (hD : riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * m - 2) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => s.1.2 + 1 = m)).card ≤ 2 := by
  rw [riccatiActualMonomialSlotFinset_topCardRecovery31Fourth]
  exact riccatiTopJetSlotMultiplicity_le_twoMinimumRecovery30Third m hm q hD

/-- The actual source monomial integral is the integral of its finite slot
product, split at order `m-1`. This is the slot-indexed form needed by the
two-top-L2 continuity theorem. -/
theorem riccatiActualMonomial_finiteSlotIntegralSplitRecovery31Fourth
    (m : ℕ) (u : ℝ → ℂ) (c : ℤ) (q : Jet →₀ ℕ) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial q c)) =
      ∫ x in (0 : ℝ)..1,
        (c : ℂ) *
          (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
            (fun s => s.1.2 + 1 = m), riccatiJetFunction u s.1 x) *
          (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
            (fun s => ¬ s.1.2 + 1 = m), riccatiJetFunction u s.1 x) := by
  apply intervalIntegral.integral_congr
  intro x hx
  calc
    riccatiJetEvaluation u x (MvPolynomial.monomial q c) =
        (c : ℂ) *
          ((q.filter (fun v : Jet => v.2 + 1 = m)).prod
            (fun v n => riccatiJetFunction u v x ^ n)) *
          ((q.filter (fun v : Jet => ¬ v.2 + 1 = m)).prod
            (fun v n => riccatiJetFunction u v x ^ n)) :=
      riccatiActualMonomial_topSlotSplitPointwiseRecovery31First m u x c q
    _ = (c : ℂ) *
          (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
            (fun s => s.1.2 + 1 = m), riccatiJetFunction u s.1 x) *
          (∏ s ∈ (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
            (fun s => ¬ s.1.2 + 1 = m), riccatiJetFunction u s.1 x) := by
      rw [← riccatiActualMonomialSlotFinset_topProd_eq_filterRecovery31Fourth,
        ← riccatiActualMonomialSlotFinset_lowerProd_eq_filterRecovery31Fourth]

end NlsGge.HierarchyRiccati.Core
