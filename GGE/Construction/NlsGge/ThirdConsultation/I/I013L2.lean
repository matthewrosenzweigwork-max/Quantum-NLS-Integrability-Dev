import Mathlib
import NlsGge.Herglotz38.PlemeljBoundaryE02_38
import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.ThirdConsultation.I.I013Weights
import NlsGge.ThirdConsultation.I.I013Bounds

                                                                                                   
                                                                                                     
                                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I.I013C

/-- Each truncation is in L^2 (for δ > 0). -/
theorem truncHilbert_memLp (v : ℝ → ℝ) (hv : Continuous v) (M A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M)
    (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun x : ℝ => ∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) 2 volume :=
  NlsGge.ThirdConsultation.I.I013A.memLp_two_of_sq_weight _
    (stronglyMeasurable_truncHilbert_E02_38 v hv δ).aestronglyMeasurable _
    (NlsGge.ThirdConsultation.I.I013B.truncHilbert_sq_weight v M A B hA hB hsupp hB' hM δ hδ)

/-- The PV transform is in L^2 when it is continuous (the continuity is supplied by the caller). -/
theorem pv_memLp (v : ℝ → ℝ) (hv : Continuous v) (H M A B : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M)
    (hpc : Continuous (pvHilbert v)) :
    MemLp (pvHilbert v) 2 volume :=
  NlsGge.ThirdConsultation.I.I013A.memLp_two_of_sq_weight _ hpc.aestronglyMeasurable _
    (fun x => NlsGge.ThirdConsultation.I.I013B.pv_sq_weight v H M A B hv hH hA hB hsupp hB' hhol hM x)

/-- L^2 convergence of the truncated Hilbert transforms to the PV transform. -/
theorem truncHilbert_sub_pv_tendsto (v : ℝ → ℝ) (hv : Continuous v) (H M A B : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M)
    (hpc : Continuous (pvHilbert v)) :
    Tendsto (fun δ : ℝ => eLpNorm
      (fun x : ℝ => (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ δ : ℝ, AEStronglyMeasurable
      (fun x : ℝ => ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2) volume :=
    fun δ => (((stronglyMeasurable_truncHilbert_E02_38 v hv δ).aestronglyMeasurable.sub
      hpc.aestronglyMeasurable)).pow 2
  have hbd : ∀ δ : ℝ, 0 < δ → ∀ x : ℝ,
      ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2 ≤
        4 * (M ^ 2 * (1 + (2 * A + 1) ^ 2) + 2 * (4 * A * B) ^ 2) * (1 + x ^ 2)⁻¹ := by
    intro δ hδ x
    have h1 := NlsGge.ThirdConsultation.I.I013B.truncHilbert_sq_weight v M A B hA hB hsupp hB' hM δ hδ x
    have h2 := NlsGge.ThirdConsultation.I.I013B.pv_sq_weight v H M A B hv hH hA hB hsupp hB' hhol hM x
    have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
    have key2 : ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2 * (1 + x ^ 2) ≤
        2 * ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) ^ 2 * (1 + x ^ 2)) +
          2 * (pvHilbert v x ^ 2 * (1 + x ^ 2)) := by
      nlinarith [mul_nonneg (sq_nonneg ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) + pvHilbert v x)) hpos.le]
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  have hsq : Tendsto (fun δ : ℝ =>
      ∫ x : ℝ, ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have key := tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := 𝓝[>] (0:ℝ))
      (F := fun δ x => ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2)
      (f := fun _ => (0:ℝ)) (fun x => 4 * (M ^ 2 * (1 + (2 * A + 1) ^ 2) + 2 * (4 * A * B) ^ 2) * (1 + x ^ 2)⁻¹)
      (Eventually.of_forall fun δ => hmeas δ)
      (eventually_nhdsWithin_of_forall fun δ hδ => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hbd δ hδ x)
      (integrable_inv_one_add_sq.const_mul _)
      (Eventually.of_forall fun x => by
        have ht := ((tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol x).sub_const (pvHilbert v x)).pow 2
        have h0 : (pvHilbert v x - pvHilbert v x) ^ 2 = 0 := by ring
        rw [h0] at ht
        exact ht)
    have e : (∫ x : ℝ, (0:ℝ)) = 0 := integral_zero _ _
    rw [e] at key
    exact key
  have hL : ∀ δ : ℝ, 0 < δ →
      eLpNorm (fun x : ℝ => (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) 2 volume =
        ENNReal.ofReal ((∫ x : ℝ, ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2)
          ^ (2⁻¹ : ℝ)) := by
    intro δ hδ
    have hm : MemLp (fun x : ℝ => (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) 2
        volume := (truncHilbert_memLp v hv M A B hA hB hsupp hB' hM δ hδ).sub
      (pv_memLp v hv H M A B hH hA hB hsupp hB' hhol hM hpc)
    rw [hm.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hreal : Tendsto (fun δ : ℝ =>
      (∫ x : ℝ, ((∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) - pvHilbert v x) ^ 2) ^ (2⁻¹ : ℝ))
      (𝓝[>] 0) (𝓝 ((0:ℝ) ^ (2⁻¹ : ℝ))) :=
    hsq.rpow_const (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at hreal
  have hof := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at hof
  refine hof.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hL δ hδ).symm

/-- Pairing limit: for integrable `g`, the truncated pairings converge to the PV pairing. -/
theorem truncHilbert_pairing_tendsto (v : ℝ → ℝ) (hv : Continuous v) (H M A B : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M)
    (g : ℝ → ℝ) (hg : Integrable g) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ, g x * (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)))
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, g x * pvHilbert v x)) := by
  have hT : ∀ x : ℝ, Tendsto (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t))
      (𝓝[>] 0) (𝓝 (pvHilbert v x)) :=
    fun x => tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol x
  refine tendsto_integral_filter_of_dominated_convergence (fun x => M * ‖g x‖)
    (F := fun δ x => g x * (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)))
    (f := fun x => g x * pvHilbert v x)
    (Eventually.of_forall fun δ => hg.aestronglyMeasurable.mul
      (stronglyMeasurable_truncHilbert_E02_38 v hv δ).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun δ hδ => Eventually.of_forall fun x => by
      rw [norm_mul, mul_comm M]
      have hb : ‖∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)‖ ≤ M := by
        rw [Real.norm_eq_abs]; exact hM x δ hδ
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    (hg.norm.const_mul M)
    (Eventually.of_forall fun x => (hT x).const_mul (g x))

end NlsGge.ThirdConsultation.I.I013C

end
