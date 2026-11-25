import NlsGge.GK38.GradEigenRealNeumann
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem closedKernel1_initial_coefficient_positive (u : PhysicalL2) (n : ℤ) :
    0 < (energy (dirState u n))⁻¹+(energy (neuState u n))⁻¹ := by
  have hD := dirState_energy_positive u n
  have hN := neuState_energy_positive u n
  exact add_pos (inv_pos.mpr hD) (inv_pos.mpr hN)

theorem closedKernel1_initial (u : PhysicalL2) (n : ℤ) :
    closedKernel1 u n t0 =
      (((energy (dirState u n))⁻¹+(energy (neuState u n))⁻¹ : ℝ) : ℂ) •
        (![1,1] : PairVec38) := by
  ext i
  fin_cases i <;>
    simp [closedKernel1,normalizedSquare,square,dirState,neuState,state_initial,
      starProd38,Complex.I_sq] <;> ring

theorem gradAntiDiscrim_initial (φ : PotPair) (z : ℂ) :
    gradAntiDiscrimCont38 φ z t0 =
      (![Complex.I*monodromyPair φ z 0 0,-Complex.I*monodromyPair φ z 1 1] : PairVec38) := by
  have hF : ext38 (fundContP φ z) (0 : ℝ)=(1 : PairMat38) := by
    rw [ext38_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl,zero_le_one⟩)]
    exact fundPair_zero φ z
  ext i
  fin_cases i <;>
    simp [gradAntiDiscrimCont38,gradAntiDiscrim38,t0,fundColumn38,hF,starProd38] <;> ring

theorem closedKernel2_initial_of_monodromy (u : PhysicalL2) (n : ℤ)
    (hM : monodromyPair (realSlice u) (gkMu u n : ℂ)=parity n • (1 : PairMat38)) :
    closedKernel2 u n t0 =
      (spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ)/
        (energy (dirState u n) : ℂ)) • (![1,1] : PairVec38)+
        parity n • (![Complex.I,-Complex.I] : PairVec38) := by
  have hA : gradAntiDiscrimCont38 (realSlice u) (gkMu u n : ℂ) t0 =
      parity n • (![Complex.I,-Complex.I] : PairVec38) := by
    rw [gradAntiDiscrim_initial,hM]
    ext i
    fin_cases i <;> simp <;> ring
  change spectralAntiDiscrimIntegral38 (realSlice u) (gkMu u n : ℂ) •
    normalizedSquare (dirState u n) t0+
    gradAntiDiscrimCont38 (realSlice u) (gkMu u n : ℂ) t0 = _
  rw [hA]
  ext i
  fin_cases i <;>
    simp [normalizedSquare,square,dirState,state_initial,starProd38,div_eq_mul_inv] <;> ring

end
end NlsGge.GK38.GradEigen38
