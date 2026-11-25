import Mathlib
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Spectral.PlaneMomentInequality38V1

/- I-007 PRODUCTION01 (proof development, AUTHOR; target NlsGge/Atomic/I/I007.lean, namespace NlsGge.ThirdConsultation.I).
   Head verbatim from followup2 STATEMENTS/I.md I-007. Proof: E02 trace theorem for the smooth field (as in A01Spectral38),
   withDensity integral lemmas, and the Jensen/Bernoulli lemma jensen_moment38 (PlaneMomentInequality38V1, B/O-free). -/
set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core NlsGge.Pilot NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff

namespace NlsGge.ThirdConsultation.I

theorem i007 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) (hM : 0 < localCharge38 U 0) :
    let u := smoothL2_38 U hU hper
    let M := localCharge38 U 0
    let σ : Measure ℝ := volume.withDensity
      (fun t => ENNReal.ofReal ((2 / (Real.pi * M)) * actualGapHeightE02_38 u t))
    IsProbabilityMeasure σ ∧
    (∀ j : ℕ, Integrable (fun t : ℝ => ((2 * t) ^ 2) ^ j) σ ∧
      (∫ t : ℝ, ((2 * t) ^ 2) ^ j ∂σ) = localCharge38 U j / M) ∧
    ∀ j : ℕ, 1 ≤ j →
      (localCharge38 U 1) ^ j / M ^ (j - 1) ≤ localCharge38 U j := by
  intro u M σ
  have tr : ∀ j : ℕ, Integrable (fun t : ℝ => (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) ∧
      localCharge38 U j = (2 / Real.pi) * ∫ t : ℝ, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t :=
    fun j => NlsGge.SpectralFoundations.actualTraceFormula_E02_38 u (smoothL2_38_sobolev U hU hper) U hU hper
      (smoothL2_38_cover_ae U hU hper) j
  have hv0 : ∀ t, 0 ≤ actualGapHeightE02_38 u t := actualGapHeightE02_38_nonneg u
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hpi : 0 < Real.pi := Real.pi_pos
  set c : ℝ := 2 / (Real.pi * M) with hc
  have hc0 : 0 < c := by positivity
  set f : ℝ → NNReal := fun t => Real.toNNReal (c * actualGapHeightE02_38 u t) with hf
  have hfm : Measurable f := (hvc.const_mul c).measurable.real_toNNReal
  have hσ : σ = volume.withDensity (fun t => (f t : ENNReal)) := rfl
  have hfv : ∀ t, ((f t : NNReal) : ℝ) = c * actualGapHeightE02_38 u t := fun t =>
    Real.coe_toNNReal _ (mul_nonneg hc0.le (hv0 t))
  have hI0 : ∫ t : ℝ, actualGapHeightE02_38 u t = Real.pi / 2 * M := by
    have h0 : M = 2 / Real.pi * ∫ t : ℝ, actualGapHeightE02_38 u t := by
      have := (tr 0).2
      simpa using this
    rw [h0]; field_simp
  have hmom : ∀ j : ℕ, Integrable (fun t : ℝ => ((2 * t) ^ 2) ^ j) σ ∧
      (∫ t : ℝ, ((2 * t) ^ 2) ^ j ∂σ) = localCharge38 U j / M := by
    intro j
    have hg : (fun t : ℝ => f t • ((2 * t) ^ 2) ^ j) =
        fun t => c * ((2 * t) ^ (2 * j) * actualGapHeightE02_38 u t) := by
      funext t; rw [NNReal.smul_def, smul_eq_mul, hfv, ← pow_mul]; ring
    refine ⟨?_, ?_⟩
    · rw [hσ, integrable_withDensity_iff_integrable_smul hfm, hg]
      exact (tr j).1.const_mul c
    · rw [hσ, integral_withDensity_eq_integral_smul hfm, hg, integral_const_mul, (tr j).2]
      simp only [hc]
      field_simp
  refine ⟨⟨?_⟩, hmom, fun j hj => ?_⟩
  · have h0 := (hmom 0).2
    have hMp : 0 < M := hM
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at h0
    have hq : localCharge38 U 0 / M = 1 := div_self hMp.ne'
    rw [hq] at h0
    have h1 : (σ Set.univ).toReal = 1 := h0
    exact (ENNReal.toReal_eq_one_iff _).1 h1
  · have key := jensen_moment38 (fun t => (2 * t) ^ 2) (actualGapHeightE02_38 u) j hj
      (fun t => by positivity) hv0 (by simpa using (tr 0).1) (by simpa using (tr 1).1) (by
        refine (tr j).1.congr (Filter.Eventually.of_forall fun t => ?_)
        simp only [← pow_mul])
    have eA : ∫ t, (2 * t) ^ 2 * actualGapHeightE02_38 u t =
        ∫ t, (2 * t) ^ (2 * 1) * actualGapHeightE02_38 u t := by simp
    have eB : ∫ t, ((2 * t) ^ 2) ^ j * actualGapHeightE02_38 u t =
        ∫ t, (2 * t) ^ (2 * j) * actualGapHeightE02_38 u t := by
      congr 1; funext t; rw [← pow_mul]
    rw [eA, eB, hI0] at key
    rw [(tr 1).2, (tr j).2]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at key ⊢
    set A := ∫ t, (2 * t) ^ (2 * 1) * actualGapHeightE02_38 u t
    set B := ∫ t, (2 * t) ^ (2 * (k + 1)) * actualGapHeightE02_38 u t
    have hMp : 0 < M := hM
    have hMeq : M = 2 / Real.pi * (Real.pi / 2 * M) := by field_simp
    rw [div_le_iff₀ (by positivity)]
    have : (2 / Real.pi * A) ^ (k + 1) = (2 / Real.pi) ^ (k + 1) * A ^ (k + 1) := mul_pow _ _ _
    rw [this]
    have hk : (2 / Real.pi) ^ (k + 1) * ((Real.pi / 2 * M) ^ k * B) =
        M ^ k * (2 / Real.pi * B) := by
      rw [pow_succ (2 / Real.pi) k]
      have : (2 / Real.pi) ^ k * (Real.pi / 2 * M) ^ k = M ^ k := by
        rw [← mul_pow]; congr 1; field_simp
      calc (2 / Real.pi) ^ k * (2 / Real.pi) * ((Real.pi / 2 * M) ^ k * B)
          = ((2 / Real.pi) ^ k * (Real.pi / 2 * M) ^ k) * (2 / Real.pi * B) := by ring
        _ = _ := by rw [this]
    calc (2 / Real.pi) ^ (k + 1) * A ^ (k + 1)
        ≤ (2 / Real.pi) ^ (k + 1) * ((Real.pi / 2 * M) ^ k * B) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = 2 / Real.pi * B * M ^ k := by rw [hk]; ring

end NlsGge.ThirdConsultation.I
