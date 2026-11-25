import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Spectral.ActualTraceFormulaE02_38
import NlsGge.Hierarchy.PlaneCoverIdentification38
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Spectral.ActualGapLabelsAgreeE02_38
import NlsGge.Spectral.ActualBoxWindowUniformE02_38
import NlsGge.Weights.Entire
import Mathlib.Tactic

/-! W2 (campaign 38): unconditional spectral identification of the complete energy
`E_W(z) = (2/π) ∫ W(2λ) v(λ) dλ` on the finite plane, and the gap/mass lower bounds. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff BigOperators

/-- The trace formula for the finite-plane field, unconditional. -/
theorem plane_trace38 (N : ℕ) (z : FourierPlane N) (j : ℕ) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 (planeL2 N z) t) ∧
    localCharge38 (planeReal N z) j =
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 (planeL2 N z) t :=
  actualTraceFormula_E02_38 (planeL2 N z)
    (by rw [show physicalFourier (planeL2 N z) = physicalFourier (planeField N z) from
        funext (physicalFourier_planeL2 N z)]
        exact sobolevSquareSummable_planeField N z 1)
    (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z)
    (planeReal_cover_ae38 N z) j

theorem plane_integrand_nonneg38 (N : ℕ) (z : FourierPlane N) (j : ℕ) (t : ℝ) :
    0 ≤ (2*t)^(2*j) * actualGapHeightE02_38 (planeL2 N z) t :=
  mul_nonneg (by rw [pow_mul]; positivity) (actualGapHeightE02_38_nonneg _ _)

theorem localCharge38_plane_nonneg (N : ℕ) (z : FourierPlane N) (j : ℕ) :
    0 ≤ localCharge38 (planeReal N z) j := by
  rw [(plane_trace38 N z j).2]
  exact mul_nonneg (by positivity) (integral_nonneg (plane_integrand_nonneg38 N z j))

theorem coeff_nonneg38 {lo up : ℝ} (c : BoundedCoefficients lo up) (j : ℕ) :
    0 ≤ c.val j / ((j.factorial : ℝ)) ^ 4 :=
  div_nonneg ((c.property.1.le).trans (c.property.2.2 j).1) (by positivity)

theorem fullEnergy38_nonneg {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) : 0 ≤ fullEnergy38 c N z :=
  tsum_nonneg fun j => mul_nonneg (coeff_nonneg38 c j) (localCharge38_plane_nonneg N z j)

theorem fullEnergy38_ge_mass {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    c.val 0 * localCharge38 (planeReal N z) 0 ≤ fullEnergy38 c N z := by
  have h := (fullEnergy38_summable c N z).le_tsum 0 (fun j _ =>
    mul_nonneg (coeff_nonneg38 c j) (localCharge38_plane_nonneg N z j))
  unfold fullEnergy38
  calc c.val 0 * localCharge38 (planeReal N z) 0
      = c.val 0 / ((Nat.factorial 0 : ℕ) : ℝ) ^ 4 * localCharge38 (planeReal N z) 0 := by simp
    _ ≤ _ := h

/-- Integrability of a pointwise nonnegative summable series of integrable functions. -/
theorem integrable_tsum_nonneg38 {F : ℕ → ℝ → ℝ} (hint : ∀ i, Integrable (F i))
    (h0 : ∀ i t, 0 ≤ F i t) (hsum : ∀ t, Summable fun i => F i t)
    (hI : Summable fun i => ∫ t, F i t) : Integrable (fun t => ∑' i, F i t) := by
  have hmeas : AEStronglyMeasurable (fun t => ∑' i, F i t) volume := by
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun n t => ∑ i ∈ Finset.range n, F i t)
      (fun n => (Finset.range n).aestronglyMeasurable_fun_sum fun i _ => (hint i).1) ?_
    exact Filter.Eventually.of_forall fun t => (hsum t).hasSum.tendsto_sum_nat
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have h1 : ∀ t, ‖∑' i, F i t‖ₑ = ∑' i, ENNReal.ofReal (F i t) := by
    intro t
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i t) (hsum t),
      Real.enorm_eq_ofReal (tsum_nonneg fun i => h0 i t)]
  simp_rw [h1]
  rw [lintegral_tsum (fun i => (hint i).1.aemeasurable.ennreal_ofReal)]
  have h2 : ∀ i, ∫⁻ t, ENNReal.ofReal (F i t) = ENNReal.ofReal (∫ t, F i t) := fun i =>
    (ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (h0 i))).symm
  simp_rw [h2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (h0 i)) hI]
  exact ENNReal.ofReal_lt_top

theorem fullEnergy38_eq_spectral {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    Integrable (fun t : ℝ => NlsGge.Weights.weight c.val (2*t) *
      actualGapHeightE02_38 (planeL2 N z) t) ∧
    fullEnergy38 c N z = (2/Real.pi) * ∫ t : ℝ, NlsGge.Weights.weight c.val (2*t) *
      actualGapHeightE02_38 (planeL2 N z) t := by
  set F : ℕ → ℝ → ℝ := fun j t =>
    c.val j / ((j.factorial : ℝ)) ^ 4 * ((2*t)^(2*j) * actualGapHeightE02_38 (planeL2 N z) t)
    with hF
  have hint : ∀ j, Integrable (F j) := fun j => (plane_trace38 N z j).1.const_mul _
  have h0 : ∀ j t, 0 ≤ F j t := fun j t =>
    mul_nonneg (coeff_nonneg38 c j) (plane_integrand_nonneg38 N z j t)
  have hIj : ∀ j, ∫ t, F j t = (Real.pi / 2) *
      (c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j) := by
    intro j
    simp only [hF]
    rw [integral_const_mul, (plane_trace38 N z j).2]
    field_simp
  have hI : Summable fun j => ∫ t, F j t := by
    simp_rw [hIj]; exact (fullEnergy38_summable c N z).mul_left _
  have hpt : ∀ t, HasSum (fun j => F j t)
      (NlsGge.Weights.weight c.val (2*t) * actualGapHeightE02_38 (planeL2 N z) t) := by
    intro t
    have hs : Summable (NlsGge.weightTerm c.val (2*t)) :=
      NlsGge.Weights.weightTerm_summable lo up c.val c.property.1
        (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) _
    have := hs.hasSum.mul_right (actualGapHeightE02_38 (planeL2 N z) t)
    convert this using 1
    · funext j
      simp only [hF, NlsGge.weightTerm, NlsGge.coefficient]; ring
    · rfl
  have hsum : ∀ t, Summable fun j => F j t := fun t => (hpt t).summable
  have hint' : Integrable (fun t => ∑' j, F j t) := integrable_tsum_nonneg38 hint h0 hsum hI
  have heq : (fun t => ∑' j, F j t) = fun t => NlsGge.Weights.weight c.val (2*t) *
      actualGapHeightE02_38 (planeL2 N z) t := funext fun t => (hpt t).tsum_eq
  rw [heq] at hint'
  refine ⟨hint', ?_⟩
  have hn : ∀ j, ∫ t, ‖F j t‖ = ∫ t, F j t := fun j => by
    congr 1; funext t; exact Real.norm_of_nonneg (h0 j t)
  have hnS : Summable fun i => ∫ a, ‖F i a‖ := by
    rw [show (fun i => ∫ a, ‖F i a‖) = fun i => ∫ t, F i t from funext hn]; exact hI
  have hs := hasSum_integral_of_summable_integral_norm hint hnS
  rw [heq] at hs
  simp_rw [hIj] at hs
  have h2 : fullEnergy38 c N z = ∑' j, c.val j / ((j.factorial : ℝ)) ^ 4 *
      localCharge38 (planeReal N z) j := rfl
  have h3 := (hs.mul_left (2 / Real.pi))
  have hz : ∀ j, 2 / Real.pi * (Real.pi / 2 * (c.val j / ((j.factorial : ℝ)) ^ 4 *
      localCharge38 (planeReal N z) j)) =
      c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j := fun j => by
    field_simp
  simp_rw [hz] at h3
  rw [h2, h3.tsum_eq]

/-! ### Gap lower bounds -/

theorem gapLower_le_upper38 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨⟨x, hx⟩, heq⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  rw [heq] at hx
  exact hx.1.trans hx.2

/-- Finite sums of integrals over distinct labelled gaps of a nonnegative integrable function
are bounded by the full integral. -/
theorem gapSum_le_integral38 (u : PhysicalL2) (f : ℝ → ℝ) (hf : Integrable f)
    (h0 : ∀ x, 0 ≤ f x) (S : Finset ℤ) :
    ∑ n ∈ S, ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x ≤
      ∫ x, f x := by
  set s : ℤ → Set ℝ := fun n => Set.Icc (actualGapLowerAllE02_38 u n)
    (actualGapUpperAllE02_38 u n) with hs
  have hsl : ∀ n, s n = actualGapLevelSetE02_38 u n := fun n =>
    (actualGapLevelSet_eq_Icc_E02_38 u n).2.symm
  have hterm : ∀ n, ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x =
      ∫ x in s n, f x := fun n => by
    rw [intervalIntegral.integral_of_le (gapLower_le_upper38 u n), hs]
    exact (integral_Icc_eq_integral_Ioc).symm
  simp_rw [hterm]
  rw [← integral_biUnion_finset S (fun n _ => measurableSet_Icc) ?_
    (fun n _ => hf.integrableOn)]
  · exact setIntegral_le_integral hf (Filter.Eventually.of_forall h0)
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    have hxa : x ∈ s a := hxa
    have hxb : x ∈ s b := hxb
    rw [hsl] at hxa hxb
    have h1 : (a:ℝ) * Real.pi = (b:ℝ) * Real.pi := (show actualQuasimomentumRealPartE02_38 u x = _ from hxa).symm.trans hxb
    exact hab (by exact_mod_cast mul_right_cancel₀ Real.pi_pos.ne' h1)

theorem fullEnergy38_ge_gapSum {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) (S : Finset ℤ) :
    ∑ n ∈ S, (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 (planeL2 N z) n)..
        (actualGapUpperAllE02_38 (planeL2 N z) n),
      NlsGge.Weights.weight c.val (2*x) * actualGapHeightE02_38 (planeL2 N z) x ≤
      fullEnergy38 c N z := by
  obtain ⟨hint, heq⟩ := fullEnergy38_eq_spectral c N z
  rw [heq, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine gapSum_le_integral38 (planeL2 N z) _ hint (fun x => ?_) S
  exact mul_nonneg (NlsGge.Weights.weight_pos lo up c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) _).le
    (actualGapHeightE02_38_nonneg _ _)

theorem fullEnergy38_gapSum_summable {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    Summable fun n : ℤ => (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 (planeL2 N z) n)..
        (actualGapUpperAllE02_38 (planeL2 N z) n),
      NlsGge.Weights.weight c.val (2*x) * actualGapHeightE02_38 (planeL2 N z) x := by
  refine summable_of_sum_le (c := fullEnergy38 c N z) (fun n => ?_)
    (fun S => fullEnergy38_ge_gapSum c N z S)
  show 0 ≤ _
  refine mul_nonneg (by positivity) ?_
  rw [intervalIntegral.integral_of_le (gapLower_le_upper38 _ n)]
  exact setIntegral_nonneg measurableSet_Ioc fun x _ =>
    mul_nonneg (NlsGge.Weights.weight_pos lo up c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) _).le
      (actualGapHeightE02_38_nonneg _ _)

theorem fullEnergy38_ge_gapTsum {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    ∑' n : ℤ, (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 (planeL2 N z) n)..
        (actualGapUpperAllE02_38 (planeL2 N z) n),
      NlsGge.Weights.weight c.val (2*x) * actualGapHeightE02_38 (planeL2 N z) x ≤
      fullEnergy38 c N z :=
  (fullEnergy38_gapSum_summable c N z).tsum_le_of_sum_le fun S => fullEnergy38_ge_gapSum c N z S

/-- Window-label form: for finitely many indices at which the box/window hypotheses hold. -/
theorem fullEnergy38_ge_gapSum_window {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) (S : Finset ℤ)
    (hS : ∀ n ∈ S, ∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ 1/1000 ∧
      ActualHalfTraceBoxE02_38 (planeL2 N z) n δ ∧
      ActualQuasimomentumWindowE02_38 (planeL2 N z) n) :
    ∑ n ∈ S, (2/Real.pi) * ∫ x in (actualGapLowerE02_38 (planeL2 N z) n)..
        (actualGapUpperE02_38 (planeL2 N z) n),
      NlsGge.Weights.weight c.val (2*x) * actualGapHeightE02_38 (planeL2 N z) x ≤
      fullEnergy38 c N z := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
    (fullEnergy38_ge_gapSum c N z S)
  obtain ⟨δ, h0, h1, hb, hw⟩ := hS n hn
  obtain ⟨hl, hu, -⟩ := actualGapLabels_agree_E02_38 (planeL2 N z) n δ h0 h1 hb hw
  rw [hl, hu]

/-- Uniform window-label form: `K` is absolute (independent of `c`, `N`, `z`, `R`). -/
theorem fullEnergy38_ge_gapSum_window_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N)
      (R : ℝ), 1 ≤ R →
      ∀ hu : SobolevSquareSummable 1 (physicalFourier (planeL2 N z)),
      ‖physicalSobolevL2 1 (planeL2 N z) hu‖ ≤ R →
      ∀ S : Finset ℤ, (∀ n ∈ S, K * R ^ 2 ≤ |(n : ℝ)|) →
      ∑ n ∈ S, (2/Real.pi) * ∫ x in (actualGapLowerE02_38 (planeL2 N z) n)..
          (actualGapUpperE02_38 (planeL2 N z) n),
        NlsGge.Weights.weight c.val (2*x) * actualGapHeightE02_38 (planeL2 N z) x ≤
        fullEnergy38 c N z := by
  obtain ⟨K, C, hK, hC, h⟩ := actualBoxWindow_uniform_E02_38
  refine ⟨K, hK, fun {lo up} c N z R hR hu hnorm S hS => ?_⟩
  refine fullEnergy38_ge_gapSum_window c N z S fun n hn => ?_
  obtain ⟨hb, hd, hw⟩ := h R hR (planeL2 N z) hu hnorm n (hS n hn)
  exact ⟨C * R ^ 2 / |(n : ℝ)|, by
    have : 0 < |(n : ℝ)| := lt_of_lt_of_le (by positivity) (hS n hn)
    positivity, hd, hb, hw⟩

end NlsGge.HierarchyRiccati.Core
