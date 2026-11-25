import NlsGge.Schur.ActualSchurRootMultiplicity38V1
import NlsGge.Schur.ActualSchurF03Package38V1
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualGapLabelsAgreeE02_38
import NlsGge.Spectral.ActualBoxWindowUniformE02_38
import Mathlib

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S


def multisetZeros (f : ℂ → ℂ) (s : Set ℂ)
    (hfinite : {z : ℂ | z ∈ s ∧ f z = 0}.Finite)
    (horder : ∀ z : ℂ, z ∈ s → f z = 0 →
      AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤) : Multiset ℂ := by
  classical
  exact ∑ z ∈ hfinite.toFinset,
    Multiset.replicate (analyticOrderAt f z).toNat z

def physicalSchurDet (n : ℤ)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (z : ℂ) : ℂ :=
  actualSchurDet38 (-n) (w, actualH1Conj38 w) (-z)

theorem highSchur_roots_labeled :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ (n : ℤ), C * R ^ 3 ≤ |(n : ℝ)| →
      ∀ (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))), ‖w‖ ≤ R →
        let f : ℂ → ℂ := physicalSchurDet n w
        let s : Set ℂ := Metric.ball ((n : ℂ) * Real.pi) (1 / 2 : ℝ)
        ∃ (hfinite : {z : ℂ | z ∈ s ∧ f z = 0}.Finite)
          (horder : ∀ z : ℂ, z ∈ s → f z = 0 →
            AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤),
        multisetZeros f s hfinite horder =
          ({(actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ),
            (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ)} :
              Multiset ℂ) := by
  obtain ⟨Kp, hKp, hpack⟩ := actualSchurF03Package38V1
  obtain ⟨K1, C1, hK1, hC1, hbw⟩ := actualBoxWindow_uniform_E02_38
  obtain ⟨hKge, -, h3, -⟩ := actualSchurShiftedRootsConstant38_ge
  set Cs := actualSchurGapLocalConstant38 with hCs
  set Kr := actualSchurShiftedRootsConstant38 with hKr
  refine ⟨max (max (max Kp K1) Kr) (2 * |Cs| + 1),
    lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro R hR n hn w hwR f s
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR3' : 0 ≤ R ^ 3 := by linarith
  have hR2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hnC : ∀ c : ℝ, c ≤ max (max (max Kp K1) Kr) (2 * |Cs| + 1) → c * R ^ 3 ≤ |(n : ℝ)| :=
    fun c hc => le_trans (mul_le_mul_of_nonneg_right hc hR3') hn
  have hnp : Kp * R ^ 3 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    exact hnC _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
  have hthr : Kr * R ^ 3 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    exact hnC _ (le_trans (le_max_right _ _) (le_max_left _ _))
  have hnw : K1 * R ^ 2 ≤ |(n : ℝ)| := by
    have := hnC K1 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
    exact le_trans (mul_le_mul_of_nonneg_left hR2 hK1.le) this
  have hnCs : (2 * |Cs| + 1) * R ^ 3 ≤ |(n : ℝ)| := hnC _ (le_max_right _ _)
  set U := physicalH1ComplexCarrierToL2Actual22 w with hU
  have hu := physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w
  have hnorm : ‖physicalSobolevL2 1 U hu‖ ≤ R := by
    rw [physicalSobolevL2_norm_h1Carrier38]; exact hwR
  obtain ⟨lp, lm, hle, ⟨hlpI, hlpF⟩, ⟨hlmI, hlmF⟩, hroots, hAlp, hAlm, hsimple, hdouble⟩ :=
    actualSchurDet38_realType_multiplicity38 R hR (-n) hthr w hwR
  obtain ⟨-, hall⟩ := hpack R hR (-n) hnp w hwR
  obtain ⟨⟨hlp_eq, hlm_eq⟩, -, ⟨hc1, hc2⟩, -⟩ := hall lp lm hlpI hlpF hlmI hlmF
  obtain ⟨hbox, hδ, hwin⟩ := hbw R hR U hu hnorm n hnw
  obtain ⟨hlo, hup, -⟩ := actualGapLabels_agree_E02_38 U n _ (by positivity) hδ hbox hwin
  simp only [neg_neg, Int.cast_neg, abs_neg] at hlp_eq hlm_eq hc1 hc2
  rw [hlo] at hlp_eq hc1
  rw [hup] at hlm_eq hc2
  set a := actualGapLowerAllE02_38 U n with ha
  set b := actualGapUpperAllE02_38 U n with hb
  have hca : |a - (n : ℝ) * Real.pi| ≤ Cs * R ^ 3 / |(n : ℝ)| := by
    convert hc1 using 2; ring
  have hcb : |b - (n : ℝ) * Real.pi| ≤ Cs * R ^ 3 / |(n : ℝ)| := by
    convert hc2 using 2; ring
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by
    have : 0 < (2 * |Cs| + 1) * R ^ 3 := by positivity
    linarith
  have hsmall : Cs * R ^ 3 / |(n : ℝ)| < 1 / 2 := by
    rw [div_lt_iff₀ hn0]
    have h1 : Cs * R ^ 3 ≤ |Cs| * R ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) hR3'
    nlinarith [abs_nonneg Cs]
  have hca' : |a - (n : ℝ) * Real.pi| < 1 / 2 := lt_of_le_of_lt hca hsmall
  have hcb' : |b - (n : ℝ) * Real.pi| < 1 / 2 := lt_of_le_of_lt hcb hsmall
  have hmem : ∀ x : ℝ, |x - (n : ℝ) * Real.pi| < 1 / 2 → (x : ℂ) ∈ s := by
    intro x hx
    change (x : ℂ) ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (1 / 2 : ℝ)
    rw [Metric.mem_ball, dist_eq_norm]
    have e : (x : ℂ) - (n : ℂ) * (Real.pi : ℂ) = ((x - (n : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have hlpC : (lp : ℂ) = -(a : ℂ) := by rw [hlp_eq]; push_cast; ring
  have hlmC : (lm : ℂ) = -(b : ℂ) := by rw [hlm_eq]; push_cast; ring
  let g : ℂ → ℂ := fun z => actualSchurDet38 (-n) (w, actualH1Conj38 w) z
  have hfg : ∀ z, f z = g (-z) := fun z => rfl
  have hdisk : ∀ z ∈ s, (-z) ∈ spectralDisk (-n) := by
    intro z hz
    change ‖-z - spectralCenter (-n)‖ ≤ 1
    have hz' : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ < 1 / 2 := by
      have := hz
      change z ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (1 / 2 : ℝ) at this
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have e : -z - spectralCenter (-n) = -(z - (n : ℂ) * (Real.pi : ℂ)) := by
      simp [spectralCenter]; ring
    rw [e, norm_neg]; linarith
  have hz_iff : ∀ z ∈ s, (f z = 0 ↔ z = (a : ℂ) ∨ z = (b : ℂ)) := by
    intro z hz
    rw [hfg, hroots (-z) (hdisk z hz), hlpC, hlmC, neg_inj, neg_inj]
  have hset : {z : ℂ | z ∈ s ∧ f z = 0} = {(a : ℂ), (b : ℂ)} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, hf⟩; exact (hz_iff z hz).1 hf
    · intro hz
      have hzs : z ∈ s := by
        rcases hz with rfl | rfl
        · exact hmem a hca'
        · exact hmem b hcb'
      exact ⟨hzs, (hz_iff z hzs).2 hz⟩
  have hfin : {z : ℂ | z ∈ s ∧ f z = 0}.Finite := by
    rw [hset]; exact Set.toFinite _
  have hneg : deriv (fun z : ℂ => -z) = fun _ => (-1 : ℂ) := by
    funext z; simp
  have hord : ∀ z : ℂ, analyticOrderAt f z = analyticOrderAt g (-z) := by
    intro z
    have := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => -z) (z₀ := z)
      (by fun_prop) (by simp)
    exact this
  have han : ∀ z : ℂ, AnalyticAt ℂ g (-z) → AnalyticAt ℂ f z := fun z h =>
    h.comp (show AnalyticAt ℂ (fun z : ℂ => -z) z by fun_prop)
  have hgo : analyticOrderAt g (lp : ℂ) ≠ ⊤ ∧ analyticOrderAt g (lm : ℂ) ≠ ⊤ := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · obtain ⟨-, h1, h2⟩ := hsimple hlt
      rw [h1, h2]; simp
    · have h2 := hdouble heq
      rw [h2, heq, h2]; simp
  have ea : -(a : ℂ) = (lp : ℂ) := by rw [hlpC]
  have eb : -(b : ℂ) = (lm : ℂ) := by rw [hlmC]
  have hhorder : ∀ z : ℂ, z ∈ s → f z = 0 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤ := by
    intro z hz hf
    rcases (hz_iff z hz).1 hf with rfl | rfl
    · exact ⟨han _ (by rw [ea]; exact hAlp), by rw [hord, ea]; exact hgo.1⟩
    · exact ⟨han _ (by rw [eb]; exact hAlm), by rw [hord, eb]; exact hgo.2⟩
  refine ⟨hfin, hhorder, ?_⟩
  have htf : hfin.toFinset = ({(a : ℂ), (b : ℂ)} : Finset ℂ) := by
    ext z
    simp only [Set.Finite.mem_toFinset, hset, Set.mem_insert_iff, Set.mem_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  unfold multisetZeros
  rw [htf]
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hab : (a : ℂ) ≠ (b : ℂ) := by
      intro h
      have : a = b := by exact_mod_cast h
      rw [hlp_eq, hlm_eq, this] at hlt
      exact lt_irrefl _ hlt
    rw [Finset.sum_pair hab, hord, hord, ea, eb]
    obtain ⟨-, h1, h2⟩ := hsimple hlt
    rw [h1, h2]
    simp [Multiset.insert_eq_cons]
  · have hab : a = b := by
      rw [hlp_eq, hlm_eq] at heq
      linarith
    rw [← hab]
    have h2 := hdouble heq
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
    rw [hord, ea, h2]
    simp [Multiset.insert_eq_cons]

end NlsGge.ThirdConsultation.S
