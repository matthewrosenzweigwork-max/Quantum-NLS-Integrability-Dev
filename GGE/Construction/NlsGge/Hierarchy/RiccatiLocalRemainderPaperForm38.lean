import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Hierarchy.RiccatiDerivativeParseval38
import Mathlib.Tactic

/-! Batch 38, F03.06: the smooth-field identity of the realized local
remainder in the source form of `B:eq:Vm` (paper/v2.tex lines 603-611):
`W_m(r) = Σ_{j ≤ m} β_j r^{2j}`, `a_{m,n} = W_m(2πn)`,
`V_m(u) = E_m(u) - Σ_n a_{m,n} |û(n)|²`, with `E_m = Σ β_j Q_{2j}`.

Here `Q_{2j}` is the real part of the local charge `∫₀¹ (-1)^{j+1} u p_{2j+1}`
(lines 956-959); its identification with the spectral charge is E06.06. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- `W_m(r) = Σ_{j=0}^m β_j r^{2j}` (`B:eq:finitehierarchy`). -/
def finiteHierarchyW38 (M : ℕ) (β : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), β j * r ^ (2 * j)

/-- `a_{m,n} = W_m(2πn)` (`B:eq:finitehierarchy`). -/
def finiteHierarchyRate38 (M : ℕ) (β : ℕ → ℝ) (n : ℤ) : ℝ :=
  finiteHierarchyW38 M β (2 * Real.pi * n)

/-- `E_m(u) = Σ_{j ≤ m} β_j Q_{2j}(u)` with the local charge (real part). -/
def localEnergy38 (M : ℕ) (β : ℕ → ℝ) (u : ℝ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), β j *
    (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (formalChargeIntegrand j)).re

/-- The physical Fourier coefficient `û(n)` of a smooth period-one field. -/
def smoothFourier38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (n : ℤ) : ℂ :=
  physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
    (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n

theorem two_pi_abs_pow_even38 (n : ℤ) (j : ℕ) :
    (2 * Real.pi * |(n : ℝ)|) ^ (2 * j) = (2 * Real.pi * (n : ℝ)) ^ (2 * j) := by
  rw [pow_mul, pow_mul, mul_pow, mul_pow (2 * Real.pi) (n : ℝ), sq_abs]

/-- F03.06, source form. For `m ≥ 2` (the source range, line 603), every
smooth period-one field `u` and its Sobolev element `x`: the series
`Σ_n a_{m,n} |û(n)|²` converges and
`V(x) = E_m(u) - Σ_n a_{m,n} |û(n)|²`. -/
theorem localRemainderSobolev38_smooth_paperForm (M : ℕ) (hM : 2 ≤ M) (β : ℕ → ℝ)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((M - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        smoothFourier38 u hu hper n) :
    Summable (fun n : ℤ => finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) ∧
      localRemainderSobolev38 M β (toCarrier38 _ x) =
        localEnergy38 M β u -
          ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2 := by
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
  have hsum : Summable (fun n : ℤ => ∑ j ∈ Finset.range (M + 1), c j n) :=
    summable_sum hcs
  refine ⟨hfun ▸ hsum, ?_⟩
  rw [hfun, Summable.tsum_finsetSum hcs,
    localRemainderSobolev38_smooth M hM β u hu hper x hsource, localEnergy38,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(hP j).2, hc]
  simp only
  rw [tsum_mul_left, mul_sub]
  rfl

/-- Packaged existence form: for every smooth period-one field there is an
`H^{m-1}` element with its Fourier coefficients satisfying the source
identity. -/
theorem localRemainderSobolev38_smooth_paperForm_exists (M : ℕ) (hM : 2 ≤ M)
    (β : ℕ → ℝ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    ∃ x : SobolevHilbert ((M - 1 : ℕ) : ℝ),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        smoothFourier38 u hu hper n) ∧
      Summable (fun n : ℤ => finiteHierarchyRate38 M β n *
        ‖smoothFourier38 u hu hper n‖ ^ 2) ∧
      localRemainderSobolev38 M β (toCarrier38 _ x) =
        localEnergy38 M β u -
          ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2 := by
  obtain ⟨x, hx, -⟩ := riccatiSmoothPeriodicJetsAgreePointwiseRecovery31Second (M - 1) u hu hper
  exact ⟨x, hx, localRemainderSobolev38_smooth_paperForm M hM β u hu hper x hx⟩

end NlsGge.HierarchyRiccati.Core

end
