import NlsGge.GK38.PoissonMixedRootData

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem analyticOnNhd_dir_dslope38 (φ : PotPair) (z : ℂ) :
    AnalyticOnNhd ℂ (dslope (dirichletChar φ) z) univ := by
  intro ζ _
  by_cases he : ζ = z
  · subst ζ
    obtain ⟨p,hp⟩ := analyticOnNhd_dirichletChar_z φ z (mem_univ _)
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℂ (fun w : ℂ =>
        (dirichletChar φ w-dirichletChar φ z)/(w-z)) ζ :=
      ((analyticOnNhd_dirichletChar_z φ ζ (mem_univ _)).sub analyticAt_const).div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr he)
    apply hq.congr
    exact (dslope_eventuallyEq_slope_of_ne (dirichletChar φ) he).symm.mono
      (fun w hw => by simpa only [slope_def_field] using hw)

theorem dirInterpolation_off_root38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z = 0) (hne : ζ ≠ z) :
    dirInterpolation38 φ z ζ =
      dirichletChar φ ζ / ((ζ-z)*deriv (dirichletChar φ) z) := by
  simp only [dirInterpolation38,dslope_of_ne _ hne,slope_def_field,hr,sub_zero]
  rw [div_div]

theorem dirichletInterpolationTarget : DirichletInterpolationTarget := by
  intro φ z hr hs
  have ha : AnalyticOnNhd ℂ (dirInterpolation38 φ z) univ := by
    convert! (analyticOnNhd_dir_dslope38 φ z).div_const
      (c := deriv (dirichletChar φ) z) using 1
  have hv : dirInterpolation38 φ z z = 1 := by
    simp only [dirInterpolation38,dslope_same,div_self hs]
  refine ⟨ha,hv,fun ζ hne => dirInterpolation_off_root38 φ z ζ hr hne,?_⟩
  intro w hw
  split_ifs with he
  · simpa only [he] using hv
  · rw [dirInterpolation_off_root38 φ z w hr he,hw,zero_div]

end
end NlsGge.GK38.PoissonMixed38
