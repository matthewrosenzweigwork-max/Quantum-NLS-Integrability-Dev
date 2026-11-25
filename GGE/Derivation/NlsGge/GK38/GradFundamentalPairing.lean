import NlsGge.GK38.GradFundamentalDefs

/-! # K1: integral-defined complex bilinear functionals on potential pairs.
GK Chapter I, Proposition 3.1 and Corollary 3.2. Selected Lp representatives are
used through a.e. linearity. These definitions are independent of differentiation.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

abbrev PairKernelCont38 := C(Set.Icc (0 : ℝ) 1, PairVec38)

def pairKernelExt38 (g : PairKernelCont38) : ℝ → PairVec38 :=
  Set.IccExtend zero_le_one g

theorem continuous_pairKernelExt38 (g : PairKernelCont38) : Continuous (pairKernelExt38 g) :=
  g.continuous.Icc_extend'

theorem pairKernelExt38_of_mem (g : PairKernelCont38) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : pairKernelExt38 g s = g ⟨s, hs⟩ :=
  Set.IccExtend_of_mem _ _ hs

theorem norm_pairKernelExt38_le (g : PairKernelCont38) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (i : Fin 2) : ‖pairKernelExt38 g s i‖ ≤ ‖g‖ := by
  rw [pairKernelExt38_of_mem g hs]
  exact (norm_le_pi_norm (g ⟨s, hs⟩) i).trans (g.norm_coe_le_norm _)

def pairIntegral38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) (h : PotPair) : ℂ :=
  ∫ s in (0 : ℝ)..(t : ℝ),
    pairKernelExt38 g s 0 * potRepFst38 h s + pairKernelExt38 g s 1 * potRepSnd38 h s

theorem intervalIntegrable_pairKernel38 (g : PairKernelCont38)
    (t : Set.Icc (0 : ℝ) 1) (h : PotPair) :
    IntervalIntegrable (fun s => pairKernelExt38 g s 0 * potRepFst38 h s +
      pairKernelExt38 g s 1 * potRepSnd38 h s) volume 0 (t : ℝ) := by
  have hc (i : Fin 2) : Continuous (fun s => pairKernelExt38 g s i) :=
    (continuous_apply i).comp (continuous_pairKernelExt38 g)
  exact (((intervalIntegrable_coverRep38_one h.1).continuousOn_mul
    (hc 0).continuousOn).add ((intervalIntegrable_coverRep38_one h.2).continuousOn_mul
      (hc 1).continuousOn)).mono_set (uIcc_zero_subset t.2)

theorem norm_pairIntegral38_le (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1)
    (h : PotPair) : ‖pairIntegral38 g t h‖ ≤ (2 * ‖g‖) * ‖h‖ := by
  have hw := (intervalIntegrable_potW38 h).mono_set (uIcc_zero_subset t.2)
  have hbound : ‖pairIntegral38 g t h‖ ≤ ∫ s in (0 : ℝ)..(t : ℝ), ‖g‖ * potW38 h s := by
    apply intervalIntegral.norm_integral_le_of_norm_le t.2.1
    · apply Filter.Eventually.of_forall
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans t.2.2⟩
      calc _ ≤ ‖pairKernelExt38 g s 0 * potRepFst38 h s‖ +
          ‖pairKernelExt38 g s 1 * potRepSnd38 h s‖ := norm_add_le _ _
        _ ≤ ‖g‖ * ‖potRepFst38 h s‖ + ‖g‖ * ‖potRepSnd38 h s‖ := by
          simp only [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right (norm_pairKernelExt38_le g hs' 0)
            (norm_nonneg _)) (mul_le_mul_of_nonneg_right (norm_pairKernelExt38_le g hs' 1)
              (norm_nonneg _))
        _ = _ := by simp only [potW38]; ring
    · exact hw.const_mul _
  have hmono : (∫ s in (0 : ℝ)..(t : ℝ), potW38 h s) ≤ potL1Norm38 h :=
    intervalIntegral.integral_mono_interval le_rfl t.2.1 t.2.2
      (Filter.Eventually.of_forall (fun s => by simp [potW38]; positivity))
      (intervalIntegrable_potW38 h)
  calc _ ≤ _ := hbound
    _ = ‖g‖ * ∫ s in (0 : ℝ)..(t : ℝ), potW38 h s := intervalIntegral.integral_const_mul _ _
    _ ≤ ‖g‖ * (2 * ‖h‖) := mul_le_mul_of_nonneg_left
      (hmono.trans (potL1Norm38_le_two_mul h)) (norm_nonneg _)
    _ = _ := by ring

theorem pairIntegral38_add (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1)
    (h k : PotPair) : pairIntegral38 g t (h + k) = pairIntegral38 g t h + pairIntegral38 g t k := by
  have hae : (fun s => pairKernelExt38 g s 0 * potRepFst38 (h + k) s +
      pairKernelExt38 g s 1 * potRepSnd38 (h + k) s) =ᵐ[volume]
      (fun s => (pairKernelExt38 g s 0 * potRepFst38 h s + pairKernelExt38 g s 1 * potRepSnd38 h s) +
        (pairKernelExt38 g s 0 * potRepFst38 k s + pairKernelExt38 g s 1 * potRepSnd38 k s)) := by
    filter_upwards [coverRep38_add_ae h.1 k.1, coverRep38_add_ae h.2 k.2] with s h0 h1
    simp only [potRepFst38, potRepSnd38, Prod.fst_add, Prod.snd_add, h0, h1]
    ring
  unfold pairIntegral38
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  exact intervalIntegral.integral_add (intervalIntegrable_pairKernel38 g t h)
    (intervalIntegrable_pairKernel38 g t k)

theorem pairIntegral38_smul (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1)
    (c : ℂ) (h : PotPair) : pairIntegral38 g t (c • h) = c • pairIntegral38 g t h := by
  have hae : (fun s => pairKernelExt38 g s 0 * potRepFst38 (c • h) s +
      pairKernelExt38 g s 1 * potRepSnd38 (c • h) s) =ᵐ[volume]
      (fun s => c * (pairKernelExt38 g s 0 * potRepFst38 h s +
        pairKernelExt38 g s 1 * potRepSnd38 h s)) := by
    filter_upwards [coverRep38_smul_ae c h.1, coverRep38_smul_ae c h.2] with s h0 h1
    change pairKernelExt38 g s 0 * coverRep38 (c • h.1) s +
      pairKernelExt38 g s 1 * coverRep38 (c • h.2) s = _
    rw [h0, h1]
    dsimp [potRepFst38, potRepSnd38]
    ring
  unfold pairIntegral38
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs)]
  exact intervalIntegral.integral_const_mul c _

/-- The continuous linear map constructed directly from its bilinear integral. -/
def integralPairCLM38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) : PotPair →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := pairIntegral38 g t
      map_add' := pairIntegral38_add g t
      map_smul' := fun c h => pairIntegral38_smul g t c h }
    (2 * ‖g‖) (norm_pairIntegral38_le g t)

@[simp] theorem integralPairCLM38_apply (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1)
    (h : PotPair) : integralPairCLM38 g t h = pairIntegral38 g t h := rfl

theorem integralPairCLM38_unique (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1)
    (L : PotPair →L[ℂ] ℂ) (hL : ∀ h, L h = pairIntegral38 g t h) : L = integralPairCLM38 g t := by
  apply ContinuousLinearMap.ext
  intro h
  exact hL h

end
end NlsGge.GK38
