import NlsGge.GK38.GradEigenClosedSpectral
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem dirichlet_offdiag_scalar_and_endpoint (u : PhysicalL2) (n : ℤ)
    (h01 : monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1=0) :
    (∃ upper : Bool, gkMu u n=endpoint u n upper) ∧
    monodromyPair (realSlice u) (gkMu u n : ℂ)=parity n • (1 : PairMat38) := by
  let M := monodromyPair (realSlice u) (gkMu u n : ℂ)
  have h10 : M 1 0=0 := by
    have hs := monodromyPair_real_entry_star38 u (gkMu u n) 0 1
    rw [h01,star_zero] at hs
    exact hs.symm
  have hb := dirichlet_boundary_sum (realSlice u) (gkMu u n : ℂ) (gkMu_root38 u n)
  change M 0 1=0 at h01
  have heq : M 1 1=M 0 0 := by
    change M 1 0+M 1 1-M 0 0-M 0 1=0 at hb
    rw [h01,h10] at hb
    linear_combination hb
  have hdet := monodromy_det_scalar (realSlice u) (gkMu u n : ℂ)
  change M 0 0*M 1 1-M 0 1*M 1 0=1 at hdet
  rw [h01,h10,heq] at hdet
  have hroot : perChar (realSlice u) (gkMu u n : ℂ)=0 := by
    rw [perChar_eq,discrim_eq]
    change (M 0 0+M 1 1)^2-4=0
    rw [heq]
    linear_combination 4*hdet
  have hlevel : actualQuasimomentumRealPartE02_38 u (gkMu u n)=(n : ℝ)*Real.pi := by
    have hm := gkMu_mem_gap38 u n
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2] at hm
    exact hm
  have hep : ∃ upper : Bool, gkMu u n=endpoint u n upper := by
    obtain h|h := perChar_root_eq_level_endpoint38 u (gkMu u n) n hroot hlevel
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  refine ⟨hep,?_⟩
  obtain ⟨upper,hu⟩ := hep
  have ht := endpoint_discrim_value u n upper
  rw [← hu,discrim_eq] at ht
  change M 0 0+M 1 1=2*parity n at ht
  have hdiag : M 0 0=parity n := by linear_combination ht/2-heq/2
  change M=parity n • (1 : PairMat38)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01,h10,heq,hdiag]

theorem offdiag_zero_implies_closed (u : PhysicalL2) (n : ℤ)
    (h01 : monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1=0) : u ∈ Z n := by
  obtain ⟨⟨upper,hu⟩,hM⟩ := dirichlet_offdiag_scalar_and_endpoint u n h01
  have hd := periodic_scalar_spectral_deriv_zero (realSlice u) (gkMu u n : ℂ) (parity n) hM
  change actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n
  by_contra hc
  have hgap := lt_of_le_of_ne (gap_endpoint_levels38 u n).1 hc
  have hn := endpoint_discrim_deriv_ne_zero u n upper hgap
  rw [← hu] at hn
  exact hn hd

def ClosedMonodromyTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ), u ∈ Z n ↔
    monodromyPair (realSlice u) (gkMu u n : ℂ)=parity n • (1 : PairMat38)

def ClosedOffDiagonalTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ), u ∈ Z n ↔
    monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1=0

def ClosedZeroSetTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ), u ∈ Z n ↔ closedEquations n u=0

def ClosedKernelInitialValuesTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    0 < (energy (dirState u n))⁻¹+(energy (neuState u n))⁻¹ ∧
    closedKernel1 u n t0 =
      (((energy (dirState u n))⁻¹+(energy (neuState u n))⁻¹ : ℝ) : ℂ) • (![1,1] : PairVec38) ∧
    (u ∈ Z n → closedKernel2 u n t0 =
      (spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ)/
        (energy (dirState u n) : ℂ)) • (![1,1] : PairVec38)+
        parity n • (![Complex.I,-Complex.I] : PairVec38))

theorem closed_monodromy_target : ClosedMonodromyTarget := by
  intro u n
  constructor
  · intro hc
    exact (dirichlet_offdiag_scalar_and_endpoint u n (closed_offdiag_zero u n hc)).2
  · intro hM
    apply offdiag_zero_implies_closed u n
    rw [hM]
    simp

theorem closed_offdiagonal_target : ClosedOffDiagonalTarget := by
  intro u n
  exact ⟨closed_offdiag_zero u n,offdiag_zero_implies_closed u n⟩

theorem closed_zero_set_target : ClosedZeroSetTarget := by
  intro u n
  constructor
  · intro hc
    have hmu := closed_mu_eq_lower u n hc
    have hnu : nu u n=actualGapLowerAllE02_38 u n := by
      have hm := nu_mem_gap u n
      change actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n at hc
      apply le_antisymm
      · simpa only [hc] using hm.2
      · exact hm.1
    have hA := (closed_dirichlet_anti_and_deriv_zero u n hc).1
    apply Prod.ext
    · change gkMu u n-nu u n=0
      rw [hmu,hnu,sub_self]
    · change (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re=0
      rw [hA]
      rfl
  · intro hz
    exact offdiag_zero_implies_closed u n (closed_equations_zero_implies_offdiag u n hz)

theorem closed_kernel_initial_values_target : ClosedKernelInitialValuesTarget := by
  intro u n
  refine ⟨closedKernel1_initial_coefficient_positive u n,closedKernel1_initial u n,?_⟩
  intro hc
  exact closedKernel2_initial_of_monodromy u n ((closed_monodromy_target u n).mp hc)

end
end NlsGge.GK38.GradEigen38
