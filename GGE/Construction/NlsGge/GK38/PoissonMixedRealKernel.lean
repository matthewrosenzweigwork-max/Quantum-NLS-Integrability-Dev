import NlsGge.GK38.PoissonMixedRealNormingData

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem real_state_antisymmetry38 (u : PhysicalL2) (x : ℝ) (a : PairVec38)
    (ha : a 1 = -star (a 0)) (t : Time) :
    state (realSlice u) (x : ℂ) a t 1 = -star (state (realSlice u) (x : ℂ) a t 0) := by
  simp only [state_eq_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    star_add,star_mul,fundPair_real_entry_star38,ha,star_neg,star_star]
  change _ = -(star (a 0)*fundPair (realSlice u) (x : ℂ) t 1 1 +
    -a 0*fundPair (realSlice u) (x : ℂ) t 1 0)
  ring

theorem terminalSeed_antisymmetry38 (u : PhysicalL2) (x : ℝ) :
    terminalSeed (realSlice u) (x : ℂ) 1 =
      -star (terminalSeed (realSlice u) (x : ℂ) 0) := by
  simp only [terminalSeed,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,star_add,monodromyPair_real_entry_star38]
  change -(monodromyPair (realSlice u) (x : ℂ) 0 0 +
    monodromyPair (realSlice u) (x : ℂ) 1 0) =
    -(monodromyPair (realSlice u) (x : ℂ) 1 0 +
    monodromyPair (realSlice u) (x : ℂ) 0 0)
  ring

theorem normingKernel_realSymmetric38 (u : PhysicalL2) (x : ℝ) :
    realSymmetric (normingKernel38 (realSlice u) (x : ℂ)) := by
  have hg := real_state_symmetry u x ![1,1] (by simp)
  have hk := real_state_antisymmetry38 u x (terminalSeed (realSlice u) (x : ℂ))
    (terminalSeed_antisymmetry38 u x)
  have hc : star ((2*Complex.I)⁻¹) = -((2*Complex.I)⁻¹) := by simp
  intro t
  change (2*Complex.I)⁻¹ *
      (state (realSlice u) (x : ℂ) ![1,1] t 0 *
        state (realSlice u) (x : ℂ) (terminalSeed (realSlice u) (x : ℂ)) t 0) =
    star ((2*Complex.I)⁻¹ *
      (state (realSlice u) (x : ℂ) ![1,1] t 1 *
        state (realSlice u) (x : ℂ) (terminalSeed (realSlice u) (x : ℂ)) t 1))
  rw [hg t,hk t,star_mul,hc]
  simp only [star_mul,star_neg,star_star]
  ring

theorem normingSpectral_real38 (u : PhysicalL2) (x : ℝ) :
    star (normingSpectral38 (realSlice u) (x : ℂ)) =
      normingSpectral38 (realSlice u) (x : ℂ) := by
  have hd : Differentiable ℂ (normingFactor (realSlice u)) :=
    fun z => (hasDerivAt_normingSpectral38 (realSlice u) z).differentiableAt
  have hi := (realRestriction_deriv38 _ hd (normingFactor_real_im38 u) x).2.1
  rw [(hasDerivAt_normingSpectral38 (realSlice u) (x : ℂ)).deriv] at hi
  apply Complex.ext
  · rfl
  · change -(normingSpectral38 (realSlice u) (x : ℂ)).im =
      (normingSpectral38 (realSlice u) (x : ℂ)).im
    rw [hi]
    norm_num

theorem kappaKernel_realSymmetric38 (u : PhysicalL2) (n : ℤ) :
    realSymmetric (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) := by
  have hg := dirEigenKernel38_realSymmetric u n
  have hk := normingKernel_realSymmetric38 u (gkMu u n)
  have hs := normingSpectral_real38 u (gkMu u n)
  have hc : star (2/normingFactor (realSlice u) (gkMu u n : ℂ)) =
      2/normingFactor (realSlice u) (gkMu u n : ℂ) := by
    rw [star_div₀,normingFactor_real_star38]
    norm_num
  intro t
  change (2/normingFactor (realSlice u) (gkMu u n : ℂ)) *
      (normingSpectral38 (realSlice u) (gkMu u n : ℂ) *
        dirEigenKernel38 (realSlice u) (gkMu u n : ℂ) t 1 +
        normingKernel38 (realSlice u) (gkMu u n : ℂ) t 1) = _
  rw [hg t,hk t]
  simp only [kappaKernel38,ContinuousMap.smul_apply,ContinuousMap.add_apply,
    Pi.smul_apply,Pi.add_apply,smul_eq_mul,star_mul,star_add,hc,hs]
  ring

theorem kernelHamField_realSlice38 (g : PairKernelCont38) (hg : realSymmetric g) :
    realSlice (kernelHamField38 g).1 = kernelHamField38 g := by
  apply Prod.ext
  · rfl
  change star (kernelHamField38 g).1 = (kernelHamField38 g).2
  apply physicalL2_eq_of_coverRep_Icc38
  filter_upwards [kernelHamField38_rep g,
    ae_restrict_of_ae (coverRep38_star_ae (kernelHamField38 g).1),
    ae_restrict_mem measurableSet_Icc] with s hr hs hm
  change coverRep38 (star (kernelHamField38 g).1) s = potRepSnd38 (kernelHamField38 g) s
  rw [hs]
  change star (potRepFst38 (kernelHamField38 g) s) = _
  rw [hr.1,hr.2,pairKernelExt38_of_mem _ hm,hg ⟨s,hm⟩]
  simp

end
end NlsGge.GK38.PoissonMixed38
