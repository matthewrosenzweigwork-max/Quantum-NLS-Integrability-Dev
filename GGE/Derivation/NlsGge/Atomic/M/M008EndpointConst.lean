import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008EndpointBound
import NlsGge.Atomic.M.M008EndpointPrimitive

/- M-008 SUPPORT E2d (proof development, AUTHOR; not reviewed).  Assembly: for an open own gap there is `E` such that every admissible
   endpoint curve has `HasEndpointIntegral phi p E` (R4b + R4c); the filter of the joint limit is nontrivial, so `E` is unique. -/
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

/-- The index region of the joint improper limit. -/
abbrev endpointRegion : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}

theorem endpointRegion_neBot : (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))).NeBot := by
  have h : Tendsto (fun k : ℕ => (((k : ℝ) + 4)⁻¹, ((k : ℝ) + 4)⁻¹)) atTop
      (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 4)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop)
      exact h1.prodMk_nhds h1
    · have hk : (0 : ℝ) < k + 4 := by positivity
      have h4 : ((k : ℝ) + 4)⁻¹ ≤ 4⁻¹ :=
        inv_anti₀ (by norm_num) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      refine ⟨by positivity, by positivity, ?_⟩
      show ((k : ℝ) + 4)⁻¹ + ((k : ℝ) + 4)⁻¹ < 1
      linarith [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
  exact h.neBot

theorem HasEndpointIntegral.unique {φ : PotPair} {p : ℝ → ℂ} {a b : ℂ}
    (ha : HasEndpointIntegral φ p a) (hb : HasEndpointIntegral φ p b) : a = b := by
  haveI := endpointRegion_neBot
  exact tendsto_nhds_unique ha.2 hb.2

/-- **Generic endpoint integral from a primitive.**  If `F` is a primitive of `omega` on `U`, `p` is continuous on `[0,1]`,
`C^1` on `(0,1)` with values in `U` there, and `F` has limits `l0`, `l1` along `U` at the two end points of `p`, then
`HasEndpointIntegral phi p (l1 - l0)`. -/
theorem endpointIntegral_of_primitive (φ : PotPair) (U : Set ℂ)
    (hω : ContinuousOn (omega φ) U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, HasDerivAt F (omega φ z) z)
    (p : ℝ → ℂ) (hpc : ContinuousOn p (Icc (0 : ℝ) 1)) (hpd : ContDiffOn ℝ 1 p (Ioo (0 : ℝ) 1))
    (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, p t ∈ U) (l0 l1 : ℂ)
    (h0 : Tendsto F (𝓝[U] (p 0)) (𝓝 l0)) (h1 : Tendsto F (𝓝[U] (p 1)) (𝓝 l1)) :
    HasEndpointIntegral φ p (l1 - l0) := by
  have hpdiff : ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ p t := fun t ht =>
    ((hpd t ht).contDiffAt (Ioo_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  have hderiv_cont : ContinuousOn (deriv p) (Ioo (0 : ℝ) 1) :=
    hpd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hωp : ContinuousOn (fun t => omega φ (p t)) (Ioo (0 : ℝ) 1) :=
    hω.comp (hpc.mono Ioo_subset_Icc_self) hmem
  have hcontIoo : ContinuousOn (fun t => omega φ (p t) * deriv p t) (Ioo (0 : ℝ) 1) :=
    hωp.mul hderiv_cont
  have hIcc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → Icc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
    intro ε η hε hη hεη t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hint : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      IntervalIntegrable (fun t : ℝ => omega φ (p t) * deriv p t) volume ε (1 - η) := by
    intro ε η hε hη hεη
    have hle : ε ≤ 1 - η := by linarith
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact (hcontIoo.mono (hIcc ε η hε hη hεη)).integrableOn_Icc
  have hftc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      ∫ t in ε..(1 - η), omega φ (p t) * deriv p t = F (p (1 - η)) - F (p ε) := by
    intro ε η hε hη hεη
    have hle : ε ≤ 1 - η := by linarith
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => F (p t)) (fun t ht => ?_)
      (hint ε η hε hη hεη)
    rw [uIcc_of_le hle] at ht
    have ht' := hIcc ε η hε hη hεη ht
    have h1 := (hF (p t) (hmem t ht')).scomp t (hpdiff t ht').hasDerivAt
    simp only [smul_eq_mul] at h1
    exact h1.congr_deriv (mul_comm _ _)
  refine ⟨hint, ?_⟩
  have hmem' : ∀ q ∈ endpointRegion, q.1 ∈ Ioo (0 : ℝ) 1 ∧ 1 - q.2 ∈ Ioo (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hq
    exact ⟨⟨h1, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hL : Tendsto (fun q : ℝ × ℝ => F (p q.1)) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))) (𝓝 l0) := by
    have hp_t : Tendsto (fun q : ℝ × ℝ => p q.1) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ)))
        (𝓝[U] (p 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto p (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (p 0)) :=
          (hpc 0 ⟨le_refl _, zero_le_one⟩).tendsto
        refine hc.comp ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · simpa using (continuous_fst.tendsto ((0 : ℝ), (0 : ℝ))).mono_left
            (nhdsWithin_le_nhds (s := endpointRegion))
        · filter_upwards [self_mem_nhdsWithin] with q hq
          exact Ioo_subset_Icc_self (hmem' q hq).1
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact hmem _ (hmem' q hq).1
    exact h0.comp hp_t
  have hR : Tendsto (fun q : ℝ × ℝ => F (p (1 - q.2))) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ))) (𝓝 l1) := by
    have hp_t : Tendsto (fun q : ℝ × ℝ => p (1 - q.2)) (𝓝[endpointRegion] ((0 : ℝ), (0 : ℝ)))
        (𝓝[U] (p 1)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto p (𝓝[Icc (0 : ℝ) 1] 1) (𝓝 (p 1)) :=
          (hpc 1 ⟨zero_le_one, le_refl _⟩).tendsto
        refine hc.comp ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun q : ℝ × ℝ => 1 - q.2) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (1 - (0 : ℝ))) :=
            (continuous_const.sub continuous_snd).tendsto ((0 : ℝ), (0 : ℝ))
          simpa using this.mono_left (nhdsWithin_le_nhds (s := endpointRegion))
        · filter_upwards [self_mem_nhdsWithin] with q hq
          exact Ioo_subset_Icc_self (hmem' q hq).2
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact hmem _ (hmem' q hq).2
    exact h1.comp hp_t
  refine (hR.sub hL).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (hftc q.1 q.2 hq.1 hq.2.1 hq.2.2).symm

/-- Open gap: a primitive `F` of `omega` on the cut disc with limits `l-`, `l+` at the two gap endpoints. -/
theorem omega_primitive_limits (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    ∃ (F : ℂ → ℂ) (lm lp : ℂ),
      (∀ z ∈ (gapDiscSeg φ hφ n).domain, HasDerivAt F (omega φ z) z) ∧
      Tendsto F (𝓝[(gapDiscSeg φ hφ n).domain] (lamMinus φ n)) (𝓝 lm) ∧
      Tendsto F (𝓝[(gapDiscSeg φ hφ n).domain] (lamPlus φ n)) (𝓝 lp) := by
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  obtain ⟨F, hF⟩ := omega_primitive φ hφ n
  obtain ⟨hbm, hbp⟩ := omega_endpointBound φ hφ n hne
  have hdom : D.domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  obtain ⟨lm, hlm⟩ := primitive_limit D hne (omega φ) F hf hF (lamMinus φ n) (Or.inl rfl)
    (by rw [hdom]; exact hbm)
  obtain ⟨lp, hlp⟩ := primitive_limit D hne (omega φ) F hf hF (lamPlus φ n) (Or.inr rfl)
    (by rw [hdom]; exact hbp)
  exact ⟨F, lm, lp, hF, hlm, hlp⟩

/-- Every admissible endpoint curve of an open gap has the joint improper integral `l+ - l-`. -/
theorem omega_endpointIntegral_const (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    ∃ E : ℂ, ∀ p : ℝ → ℂ, AdmissibleEndpointCurve φ n p → HasEndpointIntegral φ p E := by
  set D := gapDiscSeg φ hφ n with hD
  have hf : DifferentiableOn ℂ (omega φ) D.domain := omega_differentiableOn_domain φ hφ n
  obtain ⟨F, lm, lp, hF, hlm, hlp⟩ := omega_primitive_limits φ hφ n hne
  have hdom : D.domain = discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n) := rfl
  refine ⟨lp - lm, fun p hp => ?_⟩
  obtain ⟨hpc, hpd, hp0, hp1, hcase⟩ := hp
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, p t ∈ D.domain := by
    rcases hcase with h | ⟨h, -⟩
    · intro t ht; rw [hdom]; exact h t ht
    · exact absurd h hne
  refine endpointIntegral_of_primitive φ D.domain hf.continuousOn F hF p hpc hpd hmem lm lp ?_ ?_
  · rw [hp0]; exact hlm
  · rw [hp1]; exact hlp

end
end NlsGge.ThirdConsultation.MContour
