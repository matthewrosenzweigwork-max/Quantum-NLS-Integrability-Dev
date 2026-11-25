import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support3
import NlsGge.ThirdConsultation.KSPS.KSPS007Support4

                                                                                                                    
                                                                                                 
                                                                                                  
                                                                                                      
                                                                                                                 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS007Support NlsGge.ThirdConsultation.KSPS007Support3
open NlsGge.ThirdConsultation.KSPS007Support4
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS011Support3

/-- Fubini on the triangle `0 < s < t ≤ x` for the exponential Volterra kernel. -/
theorem tri_swap (c : ℂ) {h : ℝ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hh : IntervalIntegrable h volume 0 x) :
    ∫ t in (0 : ℝ)..x, c * ∫ s in (0 : ℝ)..t, Complex.exp (c * (t - s)) * h s =
      ∫ s in (0 : ℝ)..x, (Complex.exp (c * (x - s)) - 1) * h s := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) x) with hμ
  have hhi : Integrable h μ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx] at hh; exact hh
  let G : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.2 < p.1}
    (fun p => c * (Complex.exp (c * (p.1 - p.2)) * h p.2))
  have hGint : Integrable G (μ.prod μ) := by
    set C : ℝ := ‖c‖ * Real.exp (‖c‖ * x) with hC
    have hdom : Integrable (fun p : ℝ × ℝ => C * ‖h p.2‖) (μ.prod μ) := by
      have : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖h p.2‖) (μ.prod μ) := by
        refine Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun s => ‖h s‖) ?_ hhi.norm
        exact integrable_const _
      simpa [mul_comm, mul_assoc] using this.const_mul C
    refine Integrable.mono' hdom ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => c * (Complex.exp (c * (p.1 - p.2)) * h p.2))
          (μ.prod μ) := by
        refine aestronglyMeasurable_const.mul (AEStronglyMeasurable.mul ?_ ?_)
        · exact (Continuous.aestronglyMeasurable (by fun_prop))
        · exact hhi.aestronglyMeasurable.comp_quasiMeasurePreserving
            (Measure.quasiMeasurePreserving_snd)
      exact h1.indicator (measurableSet_lt measurable_snd measurable_fst)
    · have hmem : ∀ᵐ t ∂μ, t ∈ Ioc (0 : ℝ) x := ae_restrict_mem measurableSet_Ioc
      have hmem' : ∀ᵐ p ∂(μ.prod μ), p.1 ∈ Ioc (0 : ℝ) x :=
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hmem
      have hmem'' : ∀ᵐ p ∂(μ.prod μ), p.2 ∈ Ioc (0 : ℝ) x :=
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hmem
      filter_upwards [hmem', hmem''] with p hp hp2
      by_cases hlt : p.2 < p.1
      · simp only [G, Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.2 < p.1} from hlt)]
        rw [norm_mul, norm_mul, hC]
        have hu : ‖Complex.exp (c * ((p.1 : ℂ) - p.2))‖ ≤ Real.exp (‖c‖ * x) := by
          rw [Complex.norm_exp]
          calc Real.exp ((c * ((p.1 : ℂ) - p.2)).re) ≤ Real.exp ‖c * ((p.1 : ℂ) - p.2)‖ :=
                Real.exp_le_exp.2 (Complex.re_le_norm _)
            _ ≤ Real.exp (‖c‖ * x) := by
                refine Real.exp_le_exp.2 ?_
                rw [norm_mul]
                refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
                have : (p.1 : ℂ) - p.2 = ((p.1 - p.2 : ℝ) : ℂ) := by push_cast; ring
                rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
                linarith [hp.2, hp.1, hp2.1, hp2.2]
        have := mul_le_mul_of_nonneg_right hu (norm_nonneg (h p.2))
        calc ‖c‖ * (‖Complex.exp (c * ((p.1 : ℂ) - p.2))‖ * ‖h p.2‖)
            ≤ ‖c‖ * (Real.exp (‖c‖ * x) * ‖h p.2‖) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by ring
      · simp only [G, Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.2 < p.1} from hlt),
          norm_zero]
        positivity
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun t s => G (t, s)) hGint
  have hL : ∀ t ∈ Ioc (0 : ℝ) x, ∫ s, G (t, s) ∂μ =
      c * ∫ s in (0 : ℝ)..t, Complex.exp (c * (t - s)) * h s := by
    intro t ht
    have hfun : (fun s => G (t, s)) = Set.indicator (Iio t)
        (fun s => c * (Complex.exp (c * (t - s)) * h s)) := by
      funext s
      simp only [G, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio]
    rw [hfun, integral_indicator measurableSet_Iio, hμ, Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio t ∩ Ioc (0 : ℝ) x = Ioo 0 t := by
      ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le,
      intervalIntegral.integral_const_mul]
  have hR : ∀ s ∈ Ioc (0 : ℝ) x, ∫ t, G (t, s) ∂μ = (Complex.exp (c * (x - s)) - 1) * h s := by
    intro s hs
    have hfun : (fun t => G (t, s)) = Set.indicator (Ioi s)
        (fun t => (c * Complex.exp (c * (t - s))) * h s) := by
      funext t
      simp only [G, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioi]
      split_ifs <;> first | ring_nf | rfl
    rw [hfun, integral_indicator measurableSet_Ioi, hμ, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi s ∩ Ioc (0 : ℝ) x = Ioc s x := by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hs.1], h3⟩
    rw [hset, ← intervalIntegral.integral_of_le hs.2, intervalIntegral.integral_mul_const]
    congr 1
    have hd : ∀ t ∈ uIcc s x, HasDerivAt (fun t : ℝ => Complex.exp (c * ((t : ℂ) - s)))
        (c * Complex.exp (c * ((t : ℂ) - s))) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => c * ((t : ℂ) - s)) c t := by
        have := (((hasDerivAt_id t).ofReal_comp).sub_const (s : ℂ)).const_mul c
        simpa using this
      have := h1.cexp
      simpa [mul_comm] using this
    have hi : IntervalIntegrable (fun t : ℝ => c * Complex.exp (c * ((t : ℂ) - s))) volume s x := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
    simp
  rw [intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hx,
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => (hL t ht).symm),
    setIntegral_congr_fun measurableSet_Ioc (fun s hs => (hR s hs).symm)]
  exact hswap

theorem duhamel_to_integral (c : ℂ) {h F : ℝ → ℂ} (hh : IntervalIntegrable h volume 0 1)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ∀ x ∈ Icc (0 : ℝ) 1, F x = ∫ s in (0 : ℝ)..x, Complex.exp (c * (x - s)) * h s) :
    ∀ x ∈ Icc (0 : ℝ) 1, F x = ∫ t in (0 : ℝ)..x, (c * F t + h t) := by
  intro x hx
  have hsub : ∀ y ∈ Icc (0 : ℝ) 1, uIcc (0 : ℝ) y ⊆ Icc (0 : ℝ) 1 := by
    intro y hy z hz
    rw [uIcc_of_le hy.1] at hz
    exact ⟨hz.1, hz.2.trans hy.2⟩
  have hhx : ∀ y ∈ Icc (0 : ℝ) 1, IntervalIntegrable h volume 0 y := by
    intro y hy
    exact hh.mono_set (by rw [uIcc_of_le hy.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hy.2)
  have h1 : ∫ t in (0 : ℝ)..x, c * F t = ∫ t in (0 : ℝ)..x,
      c * ∫ s in (0 : ℝ)..t, Complex.exp (c * (t - s)) * h s := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htm : t ∈ Icc (0 : ℝ) 1 := hsub x hx ht
    simp only [hF t htm]
  have hFi : IntervalIntegrable F volume 0 x :=
    (hFc.mono (hsub x hx)).intervalIntegrable
  have hEi : IntervalIntegrable (fun s : ℝ => (Complex.exp (c * (x - s)) - 1) * h s) volume 0 x := by
    exact (hhx x hx).continuousOn_mul (g := fun s : ℝ => Complex.exp (c * (x - s)) - 1)
      (Continuous.continuousOn (by fun_prop))
  have hE2 : IntervalIntegrable (fun s : ℝ => Complex.exp (c * (x - s)) * h s) volume 0 x := by
    exact (hhx x hx).continuousOn_mul (g := fun s : ℝ => Complex.exp (c * (x - s)))
      (Continuous.continuousOn (by fun_prop))
  rw [intervalIntegral.integral_add (hFi.const_mul c) (hhx x hx), h1, tri_swap c hx.1 (hhx x hx),
    hF x hx, ← intervalIntegral.integral_add hEi (hhx x hx)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem comp_const (lam : ℂ) (i : Fin 2) :
    ∃ c : ℂ, (∀ u : ℝ, freeE lam u i i = Complex.exp (c * u)) ∧
      ∀ v : Fin 2 → ℂ, ((-(lam • KSPSVolterra.R)).mulVec v) i = c * v i := by
  fin_cases i
  · refine ⟨-(Complex.I * lam), fun u => ?_, fun v => ?_⟩
    · simp only [freeE, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
      congr 1; ring
    · simp [KSPSVolterra.R, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      left; ring
  · refine ⟨Complex.I * lam, fun u => ?_, fun v => ?_⟩
    · simp [freeE]
    · simp [KSPSVolterra.R, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      left; ring

theorem Fs_forcedZS (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) :
    KSPSVolterra.ForcedZS φ lam f
      (Fs (KSPSVolterra.toPair φ) lam (KSPSVolterra.forcingValue f)) := by
  set p := KSPSVolterra.toPair φ with hp
  set F := Fs p lam (KSPSVolterra.forcingValue f) with hFdef
  have hFk : ∀ k, ContinuousOn (fun s => F s k) (Set.Icc (0 : ℝ) 1) := Fs_cont p lam f
  have hFc : ContinuousOn F (Icc (0 : ℝ) 1) := continuousOn_pi.2 hFk
  refine ⟨hFc, ?_, ?_⟩
  · simp [hFdef, Fs]
  · intro x hx
    funext i
    obtain ⟨c, hc1, hc2⟩ := comp_const lam i
    set h : ℝ → ℂ := fun s => ((PCm p s).mulVec (F s)) i -
      (Rm.mulVec (KSPSVolterra.forcingValue f s)) i with hh
    have hhi : IntervalIntegrable h volume 0 1 := by
      have h1 := PCm_mulVec_ii p hFk i
      have h2 : IntervalIntegrable (fun s => (Rm.mulVec (KSPSVolterra.forcingValue f s)) i)
          volume 0 1 := by
        fin_cases i
        · simp only [Fin.zero_eta, Rm_apply0]; exact (g_ii f 0 zero_le_one).const_mul _
        · simp only [Fin.mk_one, Rm_apply1]; exact ((g_ii f 1 zero_le_one).const_mul _).neg
      exact h1.sub h2
    have hD := duhamel_to_integral c hhi (hFk i) (fun y hy => by
      refine (Fs_duhamel_comp p lam f hy i).trans ?_
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [hc1, hh]
      push_cast; rfl) x hx
    have hpt : ∀ t, ((((-(lam • KSPSVolterra.R)) + KSPSVolterra.R * KSPSVolterra.phi p t).mulVec (F t)) -
        KSPSVolterra.R.mulVec (KSPSVolterra.forcingValue f t)) i = c * F t i + h t := by
      intro t
      rw [Matrix.add_mulVec, R_mul_phi, Pi.sub_apply, Pi.add_apply, hc2]
      simp only [hh]
      rw [R_eq_Rm]
      ring
    show F x i = ∫ t in (0 : ℝ)..x, ((((-(lam • KSPSVolterra.R)) + KSPSVolterra.R * KSPSVolterra.phi p t).mulVec (F t)) -
        KSPSVolterra.R.mulVec (KSPSVolterra.forcingValue f t)) i
    simp only [hpt]
    exact hD

end NlsGge.ThirdConsultation.KSPS011Support3
