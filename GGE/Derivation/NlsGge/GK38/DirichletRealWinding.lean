import NlsGge.GK38.DirichletRealWeakPhase
import NlsGge.GK38.DirichletRealPhaseAlgebra
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.DirichletRealContinuityProbe

/-! The actual canonical clockwise winding index and its root-premiseless characterization.
Private source anchor: book I.7 Proposition 7.3. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_root_phase_integer38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    ∃ n : ℤ, phaseCandidate38 u x 1 = (n : ℝ) * Real.pi := by
  have ht := (phaseCandidate_realization38 u x).2.2 ⟨1, zero_le_one, le_rfl⟩
  have hr := (dirichlet_root_iff_endpoint_real38 u x).mp hx
  apply dirichlet_clockwise_phase_integer38
  rw [← ht.2]
  simp [Complex.div_im, hr]

theorem gkMu_winding38 (u : PhysicalL2) (n : ℤ) :
    phaseCandidate38 u (gkMu u n) 1 = (n : ℝ) * Real.pi := by
  let f : DirichletTime38 → ℝ := fun t =>
    phaseCandidate38 ((t : ℝ) • u) (gkMu ((t : ℝ) • u) n) 1 / Real.pi
  have hpot : Continuous (fun t : DirichletTime38 => (t : ℝ) • u) :=
    continuous_subtype_val.smul continuous_const
  have hpair : Continuous (fun t : DirichletTime38 =>
      ((t : ℝ) • u, gkMu ((t : ℝ) • u) n)) :=
    hpot.prodMk ((continuous_gkMu38 n).comp hpot)
  have hcomp := continuous_phaseCandidate_one38.comp hpair
  have hc : Continuous f := by
    simpa only [Function.comp_def, f] using hcomp.div_const Real.pi
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hmaps : MapsTo f univ (range ((↑) : ℤ → ℝ)) := by
    intro t _
    obtain ⟨m, hm⟩ := dirichlet_root_phase_integer38 ((t : ℝ) • u)
      (gkMu ((t : ℝ) • u) n) (gkMu_root38 _ n)
    exact ⟨m, by simp [f, hm, Real.pi_ne_zero]⟩
  obtain ⟨v, _hv, hconst⟩ := isPreconnected_univ.eqOn_const_of_mapsTo hd hc.continuousOn hmaps
    (show (range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)
  have hzero : f ⟨0, le_rfl, zero_le_one⟩ = (n : ℝ) := by
    simp only [f, zero_smul, gkMu_free38, phaseCandidate_free_one38]
    field_simp [Real.pi_ne_zero]
  have he := (hconst (mem_univ (⟨1, zero_le_one, le_rfl⟩ : DirichletTime38))).trans
    (hconst (mem_univ (⟨0, le_rfl, zero_le_one⟩ : DirichletTime38))).symm
  rw [hzero] at he
  apply (div_eq_iff Real.pi_ne_zero).mp
  simpa only [f, one_smul] using he

theorem dirichlet_phase_root_characterization38 (u : PhysicalL2) (x : ℝ) (n : ℤ) :
    phaseCandidate38 u x 1 = (n : ℝ) * Real.pi ↔ x = gkMu u n := by
  constructor
  · intro hθ
    have ht := (phaseCandidate_realization38 u x).2.2 ⟨1, zero_le_one, le_rfl⟩
    have hn : (‖dirichletState38 u (x : ℂ) ⟨1, zero_le_one, le_rfl⟩ 0‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr ht.1
    have hc := (div_eq_iff hn).mp ht.2
    have hi : (Complex.exp (-Complex.I * (phaseCandidate38 u x 1 : ℂ))).im = 0 := by
      rw [hθ]
      simp [Complex.exp_im, Complex.mul_re, Complex.mul_im, Real.sin_int_mul_pi]
    have hr := congrArg Complex.im hc
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hi,
      mul_zero, zero_mul, add_zero] at hr
    have hx := (dirichlet_root_iff_endpoint_real38 u x).mpr hr
    obtain ⟨m, hm⟩ := ((muSeq_enumeration38 (realSlice u)).2.1 (x : ℂ)).mp hx
    rw [muSeq_eq_gkMu38] at hm
    have he : gkMu u m = x := Complex.ofReal_injective hm
    have hwind := gkMu_winding38 u m
    rw [he] at hwind
    have hmn : m = n := gap_level_index_unique38 (hwind.symm.trans hθ)
    simpa only [hmn] using he.symm
  · rintro rfl
    exact gkMu_winding38 u n

theorem gkMu_global_displacement38 (u : PhysicalL2) (n : ℤ) :
    |gkMu u n - (n : ℝ) * Real.pi| ≤ ‖u‖ := by
  have h := phaseCandidate_displacement38 u (gkMu u n) ⟨1, zero_le_one, le_rfl⟩
  rw [gkMu_winding38] at h
  simpa only [mul_one, abs_sub_comm] using h

end
end NlsGge.GK38
