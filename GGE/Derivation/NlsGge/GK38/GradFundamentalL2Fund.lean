import NlsGge.GK38.GradFundamentalL2

/-! # K1: actual L2 classes of cutoff fundamental entry kernels. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem continuous_fundamentalScaledKernel38 (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    Continuous (fun s => fundamentalScaledKernel38 φ z t s i j) := by
  unfold fundamentalScaledKernel38
  split_ifs
  · exact (((continuous_starProd38 (continuous_fundColumn38 φ z 0)
      (continuous_fundColumn38 φ z 1)).neg).const_smul (fundPair φ z t i 0)).add
      ((continuous_starProd38 (continuous_fundColumn38 φ z 0)
        (continuous_fundColumn38 φ z 0)).const_smul (fundPair φ z t i 1))
  · exact (((continuous_starProd38 (continuous_fundColumn38 φ z 1)
      (continuous_fundColumn38 φ z 1)).neg).const_smul (fundPair φ z t i 0)).add
      ((continuous_starProd38 (continuous_fundColumn38 φ z 0)
        (continuous_fundColumn38 φ z 1)).const_smul (fundPair φ z t i 1))

def fundamentalEntryKernelCont38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) : PairKernelCont38 :=
  ⟨fun s => (-Complex.I) • fundamentalScaledKernel38 φ z t s i j,
    ((continuous_fundamentalScaledKernel38 φ z t i j).const_smul (-Complex.I)).comp
      continuous_subtype_val⟩

/-- Full-unit-interval kernel with the required upper-time cutoff. -/
def fundamentalEntryKernel38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) (s : ℝ) : PairVec38 :=
  if s ≤ (t : ℝ) then (-Complex.I) • fundamentalScaledKernel38 φ z t s i j else 0

def fundamentalEntryL2Class38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) : PotPair := cutoffPairKernelL2Class38 (fundamentalEntryKernelCont38 φ z t i j) t

theorem fundamentalEntryL2Class38_rep (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (fundamentalEntryL2Class38 φ z t i j) s = fundamentalEntryKernel38 φ z t i j s 0 ∧
        potRepSnd38 (fundamentalEntryL2Class38 φ z t i j) s = fundamentalEntryKernel38 φ z t i j s 1 := by
  filter_upwards [cutoffPairKernelL2Class38_rep (fundamentalEntryKernelCont38 φ z t i j) t,
    ae_restrict_mem measurableSet_Icc] with s hs hm
  have heq : cutoffPairKernel38 (fundamentalEntryKernelCont38 φ z t i j) t s =
      fundamentalEntryKernel38 φ z t i j s := by
    unfold cutoffPairKernel38 fundamentalEntryKernel38
    rw [pairKernelExt38_of_mem _ hm]
    rfl
  simpa only [fundamentalEntryL2Class38, heq] using hs

theorem potNormSq_fundamentalEntryL2Class38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    potNormSq38 (fundamentalEntryL2Class38 φ z t i j) = ∫ s in (0 : ℝ)..1,
      ‖fundamentalEntryKernel38 φ z t i j s 0‖ ^ 2 + ‖fundamentalEntryKernel38 φ z t i j s 1‖ ^ 2 := by
  rw [fundamentalEntryL2Class38, potNormSq_cutoffPairKernelL2Class38]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  change ‖cutoffPairKernel38 _ t s 0‖ ^ 2 + ‖cutoffPairKernel38 _ t s 1‖ ^ 2 = _
  unfold cutoffPairKernel38 fundamentalEntryKernel38
  rw [pairKernelExt38_of_mem _ hs]
  rfl

end
end NlsGge.GK38
