import Mathlib
import NlsGge.ThirdConsultation.S.SShared06

/- S-048 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/S/S048.lean, namespace NlsGge.ThirdConsultation.S.
   Head VERBATIM from PRO_DEFINITION_RESPONSE_FP80_06.md section 9, S-048 (entire lower weight, identity at all real r, finite reserved energy).
   Route: production reservedTerm_summable38 / sq_mul_reservedSymbol38 / reservedEnergy38_{summable,nonneg};
   B(0) by tsum_eq_single; analyticity by the power series of the shifted coefficients in r^2 with infinite radius
   (radius_eq_top_of_summable_norm), composed with r |-> r^2. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open Matrix
open scoped BigOperators Topology ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem lowerWeight_identity {lo up : ℝ} (c : BoundedCoefficients lo up) :
    (∀ r : ℝ, Summable (fun j : ℕ => NlsGge.coefficient c.val (j + 1) * r ^ (2 * j))) ∧
    (∀ r : ℝ, AnalyticAt ℝ (lowerWeightV6 c.val) r) ∧
    lowerWeightV6 c.val 0 = NlsGge.coefficient c.val 1 ∧
    (∀ r : ℝ, r ^ 2 * lowerWeightV6 c.val r =
      NlsGge.Weights.weight c.val r - NlsGge.coefficient c.val 0) ∧
    (∀ (N : ℕ) (z : FourierPlane N),
      Summable (fun j : ℕ => NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j) ∧
      0 ≤ reservedEnergy38 c N z) := by
  obtain ⟨p, hp⟩ : ∃ p : FormalMultilinearSeries ℝ ℝ ℝ,
      p = FormalMultilinearSeries.ofScalars ℝ (fun j : ℕ => NlsGge.coefficient c.val (j + 1)) :=
    ⟨_, rfl⟩
  have hrad : p.radius = ⊤ := by
    rw [hp]
    refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ fun r => ?_
    refine (reservedTerm_summable38 c (Real.sqrt (r : ℝ))).congr fun j => ?_
    simp only [FormalMultilinearSeries.ofScalars_norm]
    rw [Real.norm_of_nonneg (coefficient_nonneg_c38 c (j + 1)), pow_mul,
      Real.sq_sqrt (NNReal.coe_nonneg r)]
  have hcomp : ∀ x : ℝ, p.sum x = ∑' n : ℕ, NlsGge.coefficient c.val (n + 1) * x ^ n := by
    intro x
    rw [hp, FormalMultilinearSeries.sum]
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hg : ∀ x : ℝ, AnalyticAt ℝ p.sum x := by
    intro x
    have hpos : 0 < p.radius := by
      rw [hrad]
      simp
    have hx : x ∈ Metric.eball (0 : ℝ) p.radius := by
      rw [hrad, Metric.mem_eball]
      exact edist_lt_top _ _
    exact (p.hasFPowerSeriesOnBall hpos).analyticAt_of_mem hx
  have hanalytic : ∀ r : ℝ, AnalyticAt ℝ (lowerWeightV6 c.val) r := by
    have hfun : lowerWeightV6 c.val = fun r : ℝ => p.sum (r ^ 2) := by
      funext r
      rw [hcomp]
      unfold lowerWeightV6
      refine tsum_congr fun n => ?_
      rw [← pow_mul]
    intro r
    rw [hfun]
    have hsq : AnalyticAt ℝ (fun s : ℝ => s ^ 2) r := analyticAt_id.pow 2
    exact AnalyticAt.comp (g := p.sum) (f := fun s : ℝ => s ^ 2) (hg (r ^ 2)) hsq
  have h0 : lowerWeightV6 c.val 0 = NlsGge.coefficient c.val 1 := by
    unfold lowerWeightV6
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      rw [zero_pow (by omega : 2 * j ≠ 0), mul_zero]
  have hid : ∀ r : ℝ, r ^ 2 * lowerWeightV6 c.val r =
      NlsGge.Weights.weight c.val r - NlsGge.coefficient c.val 0 :=
    fun r => sq_mul_reservedSymbol38 c r
  exact ⟨fun r => reservedTerm_summable38 c r, hanalytic, h0, hid,
    fun N z => ⟨reservedEnergy38_summable c N z, reservedEnergy38_nonneg c N z⟩⟩

end NlsGge.ThirdConsultation.S
