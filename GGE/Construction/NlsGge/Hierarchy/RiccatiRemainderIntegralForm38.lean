import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import Mathlib.Tactic

/-! Batch 38: the finite-order Fourier remainder of `B:eq:Vm` for a smooth
period-one field, `V_m(u) = E_m(u) - Σ_n a_{m,n}|û(n)|²` (paper/v2.tex lines
603-611), and its integral form `Σ_{j≤m} β_j (Q_{2j}(u) - ∫₀¹|u^{(j)}|²)`
(via the Parseval identity `smoothDerivative_parseval38`). `Q_{2j}` is the
(real) local charge. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff

/-- `V_m(u) = E_m(u) - Σ_n a_{m,n} |û(n)|²` for a smooth period-one field. -/
def remainderV38 (M : ℕ) (β : ℕ → ℝ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) : ℝ :=
  localEnergy38 M β u -
    ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2

/-- The Fourier series in `V_m` converges, and `V_m` has the integral form
`Σ_{j≤m} β_j (Re Q^loc_{2j}(u) - ∫₀¹ |u^{(j)}|²)`. -/
theorem remainderV38_integral_form (M : ℕ) (β : ℕ → ℝ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    Summable (fun n : ℤ => finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) ∧
    remainderV38 M β u hu hper =
      ∑ j ∈ Finset.range (M + 1), β j *
        ((∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (formalChargeIntegrand j)).re -
          ∫ t in (0 : ℝ)..1, ‖iteratedDeriv j u t‖ ^ 2) := by
  have hP := fun j => smoothDerivative_parseval38 j u hu hper
  set c : ℕ → ℤ → ℝ := fun j n =>
    β j * ((2 * Real.pi * |(n : ℝ)|) ^ (2 * j) * ‖smoothFourier38 u hu hper n‖ ^ 2) with hc
  have hcs : ∀ j ∈ Finset.range (M + 1), Summable (c j) :=
    fun j _ => (hP j).1.mul_left (β j)
  have hfun : (fun n : ℤ => finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) =
      fun n => ∑ j ∈ Finset.range (M + 1), c j n := by
    funext n
    simp only [finiteHierarchyRate38, finiteHierarchyW38, Finset.sum_mul, hc,
      two_pi_abs_pow_even38]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨hfun ▸ summable_sum hcs, ?_⟩
  rw [remainderV38, hfun, Summable.tsum_finsetSum hcs, localEnergy38,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hP j).2, hc]
  simp only
  rw [tsum_mul_left, mul_sub]
  rfl

end NlsGge.HierarchyRiccati.Core

end
