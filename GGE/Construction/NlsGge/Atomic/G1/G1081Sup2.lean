import Mathlib
import NlsGge.GK38.PoissonSpectralModel
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.GradEigenClosedKernelSymmetry
import NlsGge.GK38.PoissonMixedRealKernel
import NlsGge.GK38.PoissonSpectralCommute
import NlsGge.GK38.PairRealBridgeProbe
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G1.G1081Host

                                                                                           
                                                                                                                            
                                                                                                                                                     
                                                                                                                                              
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081Sup2
noncomputable section

/-- Reality of the discriminant gradient kernel on the real slice at real spectral parameter. -/
theorem realSymmetric_gradDiscrimCont (u : PhysicalL2) (x : ℝ) :
    GradEigen38.realSymmetric (gradDiscrimCont38 (realSlice u) (x : ℂ)) := by
  intro t
  have hs (i j : Fin 2) :
      star (ext38 (fundContP (realSlice u) (x : ℂ)) (t : ℝ) i j) =
        ext38 (fundContP (realSlice u) (x : ℂ)) (t : ℝ) i.rev j.rev := by
    rw [ext38_of_mem _ t.2]
    exact fundPair_real_entry_star38 u x t i j
  have h0 : (0 : Fin 2).rev = 1 := rfl
  have h1 : (1 : Fin 2).rev = 0 := rfl
  have hI : star Complex.I = -Complex.I := by simp
  change gradDiscrim38 (realSlice u) (x : ℂ) (t : ℝ) 1 =
    star (gradDiscrim38 (realSlice u) (x : ℂ) (t : ℝ) 0)
  simp only [gradDiscrim38, starProd38, fundColumn38, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    star_mul, star_add, star_sub, star_neg, hI, monodromyPair_real_entry_star38, hs]
  simp only [h0, h1]
  ring

theorem spectralDiscrimHamField_realSlice (u : PhysicalL2) (x : ℝ) :
    realSlice (spectralDiscrimHamField38 (realSlice u) (x : ℂ)).1 =
      spectralDiscrimHamField38 (realSlice u) (x : ℂ) :=
  PoissonMixed38.kernelHamField_realSlice38 (gradDiscrimCont38 (realSlice u) (x : ℂ))
    (realSymmetric_gradDiscrimCont u x)

theorem realSlice_singleGapField (n : ℤ) (v : PhysicalL2) :
    realSlice (singleGapField n v) =
      spectralDiscrimHamField38 (realSlice v) ((gkMu v n : ℝ) : ℂ) :=
  spectralDiscrimHamField_realSlice v (gkMu v n)

theorem gradDiscrimCLM_realSlice_singleGapField (n : ℤ) (v : PhysicalL2) (z : ℂ) :
    gradDiscrimCLM (realSlice v) z (realSlice (singleGapField n v)) = 0 := by
  rw [realSlice_singleGapField, gradDiscrimCLM_spectralDiscrimHamField38,
    spectralDiscrimPoisson38_eq_zero]

theorem continuous_discrim_realSlice (z : ℂ) :
    Continuous (fun v : PhysicalL2 => discrim (realSlice v) z) :=
  Continuous.comp (g := fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2)
    (f := fun v : PhysicalL2 => (v, z)) continuous_discrim_realSlice_joint
    (Continuous.prodMk (continuous_id (X := PhysicalL2)) (continuous_const (y := z)))

/-- The discriminant along any (real multiple of the) gap flow has zero derivative. -/
theorem hasDerivWithinAt_discrim_realSlice (n : ℤ) {γ : ℝ → PhysicalL2} {s : Set ℝ} {t : ℝ}
    (c : ℝ) (z : ℂ) (h : HasDerivWithinAt γ (c • singleGapField n (γ t)) s t) :
    HasDerivWithinAt (fun r => discrim (realSlice (γ r)) z) 0 s t := by
  have h1 : HasDerivWithinAt (fun r => realSlice (γ r))
      (realSlice (c • singleGapField n (γ t))) s t :=
    realSlice.hasFDerivAt.comp_hasDerivWithinAt t h
  have h2 := ((hasFDerivAt_discrim z (realSlice (γ t))).restrictScalars ℝ).comp_hasDerivWithinAt
    t h1
  have h3 : gradDiscrimCLM (realSlice (γ t)) z (realSlice (c • singleGapField n (γ t))) = 0 := by
    rw [map_smul realSlice c]
    have := LinearMap.map_smul_of_tower (gradDiscrimCLM (realSlice (γ t)) z).toLinearMap c
      (realSlice (singleGapField n (γ t)))
    refine Eq.trans this ?_
    change c • gradDiscrimCLM (realSlice (γ t)) z (realSlice (singleGapField n (γ t))) = 0
    rw [gradDiscrimCLM_realSlice_singleGapField, smul_zero]
  rw [Function.comp_def] at h2
  simpa only [ContinuousLinearMap.coe_restrictScalars', h3] using h2

/-- S2: isospectral invariance along solutions of `γ' = c • F(γ)` on `[0,T)`. -/
theorem isospectral_of_solution_Ico (n : ℤ) {γ : ℝ → PhysicalL2} {T : ℝ} (c : ℝ)
    (h : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt γ (c • singleGapField n (γ t)) (Ico 0 T) t) :
    ∀ t ∈ Ico (0 : ℝ) T, isospectral (γ 0) (γ t) := by
  intro t ht z
  have hγc : ContinuousOn γ (Ico 0 T) := fun r hr => (h r hr).continuousWithinAt
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hg : ContinuousOn (fun r => discrim (realSlice (γ r)) z) (Icc 0 t) :=
    (continuous_discrim_realSlice z).comp_continuousOn (hγc.mono hsub)
  have key := constant_of_has_deriv_right_zero hg (fun x hx => by
    have hxT : x ∈ Ico (0 : ℝ) T := ⟨hx.1, lt_of_lt_of_le hx.2 ht.2.le⟩
    refine (hasDerivWithinAt_discrim_realSlice n c z (h x hxT)).mono_of_mem_nhdsWithin ?_
    exact mem_of_superset (Ico_mem_nhdsGE hxT.2) (fun r hr => ⟨hxT.1.trans hr.1, hr.2⟩))
    t ⟨ht.1, le_rfl⟩
  exact key

end
end NlsGge.Atomic.G1081Sup2
