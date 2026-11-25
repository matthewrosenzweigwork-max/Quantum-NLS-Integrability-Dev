import NlsGge.GK38.GradFundamentalPairing

/-! # K1: independent column-star gradient kernels.
GK Chapter I, Proposition 3.1 and Corollary 3.2. All products are bilinear.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def fundColumn38 (φ : PotPair) (z : ℂ) (s : ℝ) (j : Fin 2) : PairVec38 :=
  fun i => ext38 (fundContP φ z) s i j

def fundamentalScaledKernel38 (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1)
    (s : ℝ) (i j : Fin 2) : PairVec38 :=
  if j = 0 then
    fundPair φ z t i 0 • (-starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 1)) +
      fundPair φ z t i 1 • starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 0)
  else
    fundPair φ z t i 0 • (-starProd38 (fundColumn38 φ z s 1) (fundColumn38 φ z s 1)) +
      fundPair φ z t i 1 • starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 1)

def gradDiscrim38 (φ : PotPair) (z : ℂ) (s : ℝ) : PairVec38 :=
  (-Complex.I) • (monodromyPair φ z 0 1 • starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 0) +
    (monodromyPair φ z 1 1 - monodromyPair φ z 0 0) •
      starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 1) -
    monodromyPair φ z 1 0 • starProd38 (fundColumn38 φ z s 1) (fundColumn38 φ z s 1))

def gradAntiDiscrim38 (φ : PotPair) (z : ℂ) (s : ℝ) : PairVec38 :=
  (-Complex.I) • (monodromyPair φ z 1 1 • starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 0) +
    (monodromyPair φ z 0 1 - monodromyPair φ z 1 0) •
      starProd38 (fundColumn38 φ z s 0) (fundColumn38 φ z s 1) -
    monodromyPair φ z 0 0 • starProd38 (fundColumn38 φ z s 1) (fundColumn38 φ z s 1))

theorem continuous_fundColumn38 (φ : PotPair) (z : ℂ) (j : Fin 2) :
    Continuous (fun s => fundColumn38 φ z s j) := by
  apply continuous_pi
  intro i
  exact (continuous_apply j).comp ((continuous_apply i).comp (continuous_ext38 _))

theorem continuous_starProd38 {f g : ℝ → PairVec38} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun s => starProd38 (f s) (g s)) := by
  simp only [starProd38]
  fun_prop

theorem continuous_gradDiscrim38 (φ : PotPair) (z : ℂ) : Continuous (gradDiscrim38 φ z) := by
  unfold gradDiscrim38
  exact (((continuous_starProd38 (continuous_fundColumn38 φ z 0)
    (continuous_fundColumn38 φ z 0)).const_smul (monodromyPair φ z 0 1)).add
    ((continuous_starProd38 (continuous_fundColumn38 φ z 0)
      (continuous_fundColumn38 φ z 1)).const_smul
        (monodromyPair φ z 1 1 - monodromyPair φ z 0 0)) |>.sub
    ((continuous_starProd38 (continuous_fundColumn38 φ z 1)
      (continuous_fundColumn38 φ z 1)).const_smul (monodromyPair φ z 1 0))).const_smul (-Complex.I)

theorem continuous_gradAntiDiscrim38 (φ : PotPair) (z : ℂ) : Continuous (gradAntiDiscrim38 φ z) := by
  unfold gradAntiDiscrim38
  exact (((continuous_starProd38 (continuous_fundColumn38 φ z 0)
    (continuous_fundColumn38 φ z 0)).const_smul (monodromyPair φ z 1 1)).add
    ((continuous_starProd38 (continuous_fundColumn38 φ z 0)
      (continuous_fundColumn38 φ z 1)).const_smul
        (monodromyPair φ z 0 1 - monodromyPair φ z 1 0)) |>.sub
    ((continuous_starProd38 (continuous_fundColumn38 φ z 1)
      (continuous_fundColumn38 φ z 1)).const_smul (monodromyPair φ z 0 0))).const_smul (-Complex.I)

def gradDiscrimCont38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  ⟨fun t => gradDiscrim38 φ z t, (continuous_gradDiscrim38 φ z).comp continuous_subtype_val⟩

def gradAntiDiscrimCont38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  ⟨fun t => gradAntiDiscrim38 φ z t, (continuous_gradAntiDiscrim38 φ z).comp continuous_subtype_val⟩

/-- Independent bilinear integral definition, without differentiating Δ. -/
def gradDiscrimCLM (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  integralPairCLM38 (gradDiscrimCont38 φ z) ⟨1, zero_le_one, le_rfl⟩

/-- Independent bilinear integral definition, without differentiating δ. -/
def gradAntiDiscrimCLM (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  integralPairCLM38 (gradAntiDiscrimCont38 φ z) ⟨1, zero_le_one, le_rfl⟩

theorem gradDiscrimCLM_apply (φ : PotPair) (z : ℂ) (h : PotPair) :
    gradDiscrimCLM φ z h = ∫ s in (0 : ℝ)..1,
      gradDiscrim38 φ z s 0 * potRepFst38 h s + gradDiscrim38 φ z s 1 * potRepSnd38 h s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  simp only [pairKernelExt38_of_mem _ hs]
  rfl

theorem gradAntiDiscrimCLM_apply (φ : PotPair) (z : ℂ) (h : PotPair) :
    gradAntiDiscrimCLM φ z h = ∫ s in (0 : ℝ)..1,
      gradAntiDiscrim38 φ z s 0 * potRepFst38 h s + gradAntiDiscrim38 φ z s 1 * potRepSnd38 h s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  simp only [pairKernelExt38_of_mem _ hs]
  rfl

end
end NlsGge.GK38
