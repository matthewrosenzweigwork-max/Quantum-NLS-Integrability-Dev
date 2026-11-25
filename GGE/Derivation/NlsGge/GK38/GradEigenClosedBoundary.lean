import NlsGge.GK38.GradEigenRealNeumann
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem neumann_char_at_nu (u : PhysicalL2) (n : ℤ) :
    neumannChar38 (realSlice u) (nu u n : ℂ)=0 := by
  rw [neumannChar38_eq_dirichlet_neg,← realSlice_neg]
  exact gkMu_root38 (-u) n

theorem nu_mem_gap (u : PhysicalL2) (n : ℤ) :
    nu u n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  have h := gkMu_mem_gap38 (-u) n
  simpa only [nu,gapLower_neg38,gapUpper_neg38] using h

theorem simultaneous_boundary_offdiag (φ : PotPair) (z : ℂ)
    (hD : dirichletChar φ z=0) (hN : neumannChar38 φ z=0) (hA : antiDiscrim φ z=0) :
    monodromyPair φ z 0 1=0 := by
  have hD' := dirichlet_boundary_sum φ z hD
  rw [neumannChar38_eq] at hN
  have hN' : monodromyPair φ z 1 1-monodromyPair φ z 1 0+
      monodromyPair φ z 0 1-monodromyPair φ z 0 0=0 :=
    ((div_eq_zero_iff).mp hN).resolve_right dirichlet_denominator_ne_zero38
  change monodromyPair φ z 0 1+monodromyPair φ z 1 0=0 at hA
  linear_combination hA/2-hD'/4+hN'/4

theorem closed_equations_zero_implies_offdiag (u : PhysicalL2) (n : ℤ)
    (hz : closedEquations n u=0) : monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1=0 := by
  have hfst := congrArg Prod.fst hz
  have hsnd := congrArg Prod.snd hz
  change gkMu u n-nu u n=0 at hfst
  change (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re=0 at hsnd
  have heq : gkMu u n=nu u n := sub_eq_zero.mp hfst
  have hN := neumann_char_at_nu u n
  rw [← heq] at hN
  have hA : antiDiscrim (realSlice u) (gkMu u n : ℂ)=0 := by
    apply Complex.ext
    · exact hsnd
    · exact (dirichlet_real_characteristic38 u (gkMu u n)).2.1
  exact simultaneous_boundary_offdiag _ _ (gkMu_root38 u n) hN hA

end
end NlsGge.GK38.GradEigen38
