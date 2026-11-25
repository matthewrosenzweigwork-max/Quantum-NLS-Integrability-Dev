import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.PeriodicLabellingCriticalFree
import NlsGge.GK38.Lib.CircleArgument
import NlsGge.Atomic.M.M007
import NlsGge.Atomic.M.M008Host

/- M-008 SUPPORT S1 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Complex collapsed-gap removable extension for the
   section-10E `omega` (MContour.omega), the bridge that Pro round 6 section 10E says "the real M-007 theorem alone does not prove".
   Route: the landed M-007 proof (NlsGge/Atomic/M/M007.lean `omega_extends_collapsed`) uses the real slice only to obtain
   `lamPlus = lamMinus` from the hypothesis; every other step is stated for an arbitrary `phi in gkW`.  This file is that proof
   with the hypothesis `lamPlus phi n = lamMinus phi n` and phi in gkW taken directly.  Uses the landed M007Aux lemmas. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

theorem omega_extends_collapsed_complex (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hgap : lamPlus φ n = lamMinus φ n) :
  ∃ f : ℂ → ℂ,
    AnalyticOnNhd ℂ f (discU φ n) ∧
    (∀ z ∈ discU φ n, z ≠ lamMinus φ n → f z = omega φ z) := by
  classical
  obtain ⟨c0, N0, hgeom, hspec⟩ := isolating_family38 φ hφ
  have hn := hspec.1 n
  set lam : ℂ := lamMinus φ n with hlamdef
  have hlp : lamPlus φ n = lam := hgap
  have hseg : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (discC φ n) (discR φ n) := hn.1
  have hsegpt : segment ℝ (lamMinus φ n) (lamPlus φ n) = {lam} := by
    rw [hlp]; exact segment_same ℝ lam
  have hlamD : lam ∈ ball (discC φ n) (discR φ n) := hseg (by rw [hsegpt]; exact mem_singleton _)
  have hm_an : AnalyticOnNhd ℂ (perChar φ) univ := analyticOnNhd_perChar_z φ
  -- zero multiset information
  have hmult : (lamMinus φ n ::ₘ lamPlus φ n ::ₘ 0) =
      Lib.zeroMultiset (perChar φ) (ball (discC φ n) (discR φ n)) := hn.2.2.2.2.1
  rw [hlp] at hmult
  have hm_ball : AnalyticOnNhd ℂ (perChar φ) (closedBall (discC φ n) (discR φ n)) :=
    hm_an.mono (subset_univ _)
  have hcount : analyticOrderNatAt (perChar φ) lam = 2 := by
    have h1 := Lib.count_zeroMultiset_ball hm_ball lam
    rw [← hmult, if_pos hlamD] at h1
    rw [← h1]
    simp [hlamdef]
  have hRpos : 0 < discR φ n := (hgeom.1 n).1
  have hw : ∃ w ∈ closedBall (discC φ n) (discR φ n), perChar φ w ≠ 0 := by
    refine ⟨discC φ n + (discR φ n : ℂ), ?_, (hn.2.2.2.2.2.2.2.2.2.2.2.2 _ ?_).1⟩
    · simp [abs_of_pos hRpos]
    · simp [abs_of_pos hRpos]
  have hm0 : perChar φ lam = 0 := by
    have : lam ∈ Lib.zeroMultiset (perChar φ) (ball (discC φ n) (discR φ n)) := by
      rw [← hmult]; simp
    exact ((Lib.mem_zeroMultiset_iff_zero hm_ball ball_subset_closedBall hw).1 this).2
  have hm1 : deriv (perChar φ) lam = 0 := by
    by_contra hne
    have := (hm_an lam (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hm0 hne
    simp [analyticOrderNatAt, this] at hcount
  obtain ⟨p, hpan, hfac⟩ := NlsGge.ThirdConsultation.M.M007Aux.double_zero_factor (perChar φ) hm_an lam hm0 hm1
  have hdisc_an := analyticOnNhd_discrim_z φ
  have hΔsq : discrim φ lam ^ 2 = 4 := by
    have := hm0
    rw [perChar_eq] at this
    linear_combination this
  have hΔne : discrim φ lam ≠ 0 := by
    intro h; rw [h] at hΔsq; norm_num at hΔsq
  have hΔ' : deriv (discrim φ) lam = 0 := by
    have h1 : HasDerivAt (discrim φ) (deriv (discrim φ) lam) lam :=
      (hdisc_an lam (mem_univ _)).differentiableAt.hasDerivAt
    have hd : HasDerivAt (perChar φ) (2 * discrim φ lam * deriv (discrim φ) lam) lam := by
      have h2 := (h1.pow 2).sub_const (4 : ℂ)
      exact h2.congr_deriv (by push_cast; ring)
    have := hd.deriv
    rw [hm1] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd (by simpa using h) hΔne
    · exact h
  -- exact order two gives p lam ≠ 0
  have hord : analyticOrderAt (perChar φ) lam = 2 := by
    have := hcount
    unfold analyticOrderNatAt at this
    generalize analyticOrderAt (perChar φ) lam = k at this ⊢
    induction k using ENat.recTopCoe <;> simp_all
  obtain ⟨g, hg, hg0, hgev⟩ := ((hm_an lam (mem_univ _)).analyticOrderAt_eq_natCast (n := 2)).1
    (by simpa using hord)
  have hp0 : p lam ≠ 0 := by
    have h1 : Tendsto p (𝓝[≠] lam) (𝓝 (p lam)) :=
      (hpan lam (mem_univ _)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[≠] lam) (𝓝 (g lam)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : p =ᶠ[𝓝[≠] lam] g := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hgev, self_mem_nhdsWithin] with z hz hzl
      have hzl' : z - lam ≠ 0 := sub_ne_zero.2 hzl
      have := hfac z
      rw [hz] at this
      simp only [smul_eq_mul] at this
      exact (mul_left_cancel₀ (pow_ne_zero 2 hzl') this).symm
    have := tendsto_nhds_unique (h1.congr' hev) h2
    rw [this]; exact hg0
  -- the punctured disc avoids all gap segments
  have hnot : ∀ z ∈ ball (discC φ n) (discR φ n), z ≠ lam → z ∉ gapSegments38 φ := by
    intro z hz hzl hmem
    unfold gapSegments38 at hmem
    rw [mem_iUnion] at hmem
    obtain ⟨m, hm⟩ := hmem
    rcases eq_or_ne m n with hmn | hmn
    · subst hmn
      rw [hsegpt] at hm
      exact hzl (mem_singleton_iff.1 hm)
    · have hm' := (hspec.1 m).1 hm
      exact Set.disjoint_left.1 (isolating_geometry_disjoint38 _ _ c0 N0 hgeom hmn) hm' hz
  set G : ℂ → ℂ := fun z => canonRoot38 φ z / (z - lam) with hGdef
  have hG : AnalyticOnNhd ℂ G (ball (discC φ n) (discR φ n) \ {lam}) := by
    intro z hz
    have hzl : z ≠ lam := hz.2
    have hcr : AnalyticAt ℂ (fun w : ℂ => canonRoot38 φ w) z :=
      AnalyticAt.comp (g := fun q : PotPair × ℂ => canonRoot38 q.1 q.2) (f := fun w : ℂ => (φ, w))
        (canonRoot_analytic38 (φ, z) ⟨hφ, hnot z hz.1 hzl⟩) (analyticAt_const.prod analyticAt_id)
    exact hcr.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hzl)
  have hGp : ∀ z ∈ ball (discC φ n) (discR φ n), z ≠ lam → G z ^ 2 = p z := by
    intro z hz hzl
    have hs := canonRoot_sq38 φ hφ z (hnot z hz hzl)
    rw [hfac z] at hs
    have hzl' : z - lam ≠ 0 := sub_ne_zero.2 hzl
    simp only [hGdef]
    rw [div_pow, hs]
    field_simp
  obtain ⟨G', hG'an, hG'eq, hG'sq⟩ := NlsGge.ThirdConsultation.M.M007Aux.removable_sqrt (ball (discC φ n) (discR φ n))
    isOpen_ball lam hlamD G p hG (hpan lam (mem_univ _)).continuousAt hGp
  have hG'ne : ∀ z ∈ ball (discC φ n) (discR φ n), G' z ≠ 0 := by
    intro z hz
    by_cases hzl : z = lam
    · subst hzl
      intro h
      apply hp0
      rw [← hG'sq, h]; ring
    · rw [hG'eq z hz hzl]
      exact div_ne_zero (canonRoot_ne_zero38 φ hφ z (hnot z hz hzl)) (sub_ne_zero.2 hzl)
  have hh_an := NlsGge.ThirdConsultation.M.M007Aux.analytic_dslope (deriv (discrim φ)) (analyticOnNhd_discrimDeriv38 φ) lam
  refine ⟨fun z => dslope (deriv (discrim φ)) lam z / G' z, fun z hz => ?_, ?_⟩
  · exact (hh_an z (mem_univ _)).div (hG'an z hz) (hG'ne z hz)
  · intro z hz hzm
    have hzl : z ≠ lam := hzm
    simp only [omega]
    rw [hG'eq z hz hzl, dslope_of_ne _ hzl, slope_def_field, hΔ']
    have hzl' : z - lam ≠ 0 := sub_ne_zero.2 hzl
    have hcn := canonRoot_ne_zero38 φ hφ z (hnot z hz hzl)
    simp only [hGdef]
    field_simp
    ring


end
end NlsGge.ThirdConsultation.MContour
