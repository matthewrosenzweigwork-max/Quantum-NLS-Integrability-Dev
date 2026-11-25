import Mathlib
import NlsGge.GK38.GradFundamentalL2
import NlsGge.ThirdConsultation.G5033Host

/- G5-017 SUPPORT1 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/ThirdConsultation/G5/G5017Support1.lean, namespace NlsGge.ThirdConsultation.G5017Support1.
   Supporting lemmas for G5-017 (closing G5017_STOP.md of proof development):
   M1  Riesz bridge: pairGradientCLM (gradDiscrimCLM phi z) = gradDiscrimL2 phi z  (via the general
       pairGradientCLM (integralPairCLM38 g 1) = pairKernelL2Class38 g, Haar-circle inner product versus
       interval integral);
   M2  C-linearity and continuity of pairGradientCLM as pairGradientL : (PotPair ->L[C] C) ->L[C] PotPair;
   M3  clm_circleIntegral_comm: a continuous linear map commutes with a circle integral
       (integrability hypothesis explicit; built on ContinuousLinearMap.intervalIntegral_comp_comm). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G5017Support1
noncomputable section

/-! ### Conjugation on `PhysicalL2` -/

theorem star_add_lp (f g : PhysicalL2) : star (f + g) = star f + star g :=
  starLp.map_add f g

theorem star_smul_lp (c : ℂ) (f : PhysicalL2) :
    star (c • f) = starRingEnd ℂ c • star f := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_smul c f,
    MeasureTheory.Lp.coeFn_star (c • f),
    MeasureTheory.Lp.coeFn_smul (starRingEnd ℂ c) (star f),
    MeasureTheory.Lp.coeFn_star f] with x h1 h2 h3 h4
  simp only [h2, h3, Pi.star_apply, h1, Pi.smul_apply, h4, smul_eq_mul]
  simp

/-! ### M2: the gradient is `ℂ`-linear and continuous -/

theorem toDual_symm_comp_inl_add (L M : PotPair →L[ℂ] ℂ) :
    (InnerProductSpace.toDual ℂ PhysicalL2).symm
        ((L + M).comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) =
      (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) +
      (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (M.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) := by
  rw [ContinuousLinearMap.add_comp, map_add]

theorem toDual_symm_comp_inr_add (L M : PotPair →L[ℂ] ℂ) :
    (InnerProductSpace.toDual ℂ PhysicalL2).symm
        ((L + M).comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) =
      (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) +
      (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (M.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) := by
  rw [ContinuousLinearMap.add_comp, map_add]

theorem pairGradientCLM_add (L M : PotPair →L[ℂ] ℂ) :
    pairGradientCLM (L + M) = pairGradientCLM L + pairGradientCLM M := by
  unfold pairGradientCLM
  rw [toDual_symm_comp_inl_add, toDual_symm_comp_inr_add, star_add_lp, star_add_lp]
  rfl

theorem pairGradientCLM_smul (c : ℂ) (L : PotPair →L[ℂ] ℂ) :
    pairGradientCLM (c • L) = c • pairGradientCLM L := by
  unfold pairGradientCLM
  have h1 : (InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((c • L).comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) =
      starRingEnd ℂ c • (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) := by
    rw [ContinuousLinearMap.smul_comp, map_smulₛₗ]
  have h2 : (InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((c • L).comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) =
      starRingEnd ℂ c • (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) := by
    rw [ContinuousLinearMap.smul_comp, map_smulₛₗ]
  rw [h1, h2, star_smul_lp, star_smul_lp, Complex.conj_conj]
  rfl

theorem norm_comp_inl_le (L : PotPair →L[ℂ] ℂ) :
    ‖L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  have h := L.le_opNorm ((x, 0) : PotPair)
  have hn : ‖((x, 0) : PotPair)‖ = ‖x‖ := by simp [Prod.norm_def]
  simpa [hn] using h

theorem norm_comp_inr_le (L : PotPair →L[ℂ] ℂ) :
    ‖L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  have h := L.le_opNorm ((0, x) : PotPair)
  have hn : ‖((0, x) : PotPair)‖ = ‖x‖ := by simp [Prod.norm_def]
  simpa [hn] using h

theorem norm_pairGradientCLM_le (L : PotPair →L[ℂ] ℂ) : ‖pairGradientCLM L‖ ≤ ‖L‖ := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · change ‖star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)))‖ ≤ ‖L‖
    rw [show ∀ y : PhysicalL2, ‖star y‖ = ‖y‖ from fun y => starLp.norm_map y,
      LinearIsometryEquiv.norm_map]
    exact norm_comp_inl_le L
  · change ‖star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)))‖ ≤ ‖L‖
    rw [show ∀ y : PhysicalL2, ‖star y‖ = ‖y‖ from fun y => starLp.norm_map y,
      LinearIsometryEquiv.norm_map]
    exact norm_comp_inr_le L

/-- `pairGradientCLM` as a continuous `ℂ`-linear map. -/
def pairGradientL : (PotPair →L[ℂ] ℂ) →L[ℂ] PotPair :=
  LinearMap.mkContinuous
    { toFun := pairGradientCLM
      map_add' := pairGradientCLM_add
      map_smul' := fun c L => pairGradientCLM_smul c L }
    1 (fun L => by simpa using norm_pairGradientCLM_le L)

@[simp] theorem pairGradientL_apply (L : PotPair →L[ℂ] ℂ) :
    pairGradientL L = pairGradientCLM L := rfl

/-! ### M1: Riesz bridge for the integral-defined functionals -/

/-- Pairing with the conjugate of an interval-kernel class is the interval integral of the
kernel against the cover representative. -/
theorem inner_star_intervalKernelL2Class38 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) (x : PhysicalL2) :
    inner ℂ (star (intervalKernelL2Class38 f hf)) x =
      ∫ s in (0 : ℝ)..1, f s * coverRep38 x s := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∀ᵐ a ∂spatialMeasure,
      inner ℂ ((star (intervalKernelL2Class38 f hf) : PhysicalL2) a) (x a) =
        AddCircle.liftIoc 1 0 f a * x a := by
    filter_upwards [MeasureTheory.Lp.coeFn_star (intervalKernelL2Class38 f hf),
      (memLp_intervalKernelLift38 f hf).coeFn_toLp] with a h2 h3
    rw [RCLike.inner_apply, h2]
    have h3' : (intervalKernelL2Class38 f hf : PhysicalCircle → ℂ) a =
        AddCircle.liftIoc 1 0 f a := h3
    simp only [Pi.star_apply, h3']
    simp [mul_comm]
  have key : ∀ F : PhysicalCircle → ℂ, ∫ a, F a ∂spatialMeasure = ∫ a, F a := fun F => by
    rw [← physicalVolume_eq_spatial38]
  rw [integral_congr_ae h1, key (fun b : PhysicalCircle => AddCircle.liftIoc 1 0 f b * x b),
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0
      (fun b : PhysicalCircle => AddCircle.liftIoc 1 0 f b * x b)]
  simp only [zero_add]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [coverRep38_ae_phys x] with s hs hmem
  rw [Set.uIoc_of_le zero_le_one] at hmem
  rw [AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using hmem), hs]

theorem coverRep38_zero_ae : ∀ᵐ s : ℝ, coverRep38 (0 : PhysicalL2) s = 0 := by
  filter_upwards [coverRep38_smul_ae 0 (0 : PhysicalL2)] with s hs
  simpa using hs

theorem star_toDual_symm_integralPairCLM38_inl (g : PairKernelCont38) :
    star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩).comp
        (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))) = (pairKernelL2Class38 g).1 := by
  have h : (InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩).comp
        (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) =
      star (pairKernelL2Class38 g).1 := by
    apply ext_inner_right ℂ
    intro x
    rw [InnerProductSpace.toDual_symm_apply]
    change integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩ (x, 0) =
      inner ℂ (star (intervalKernelL2Class38 (fun s => pairKernelExt38 g s 0)
        (memLp_pairKernelExt38 g 0))) x
    rw [inner_star_intervalKernelL2Class38, integralPairCLM38_apply, pairIntegral38]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_zero_ae] with s hs _
    change pairKernelExt38 g s 0 * coverRep38 x s +
      pairKernelExt38 g s 1 * coverRep38 (0 : PhysicalL2) s = _
    rw [hs]
    ring
  rw [h, star_star]

theorem star_toDual_symm_integralPairCLM38_inr (g : PairKernelCont38) :
    star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩).comp
        (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2))) = (pairKernelL2Class38 g).2 := by
  have h : (InnerProductSpace.toDual ℂ PhysicalL2).symm
      ((integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩).comp
        (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) =
      star (pairKernelL2Class38 g).2 := by
    apply ext_inner_right ℂ
    intro x
    rw [InnerProductSpace.toDual_symm_apply]
    change integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩ (0, x) =
      inner ℂ (star (intervalKernelL2Class38 (fun s => pairKernelExt38 g s 1)
        (memLp_pairKernelExt38 g 1))) x
    rw [inner_star_intervalKernelL2Class38, integralPairCLM38_apply, pairIntegral38]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_zero_ae] with s hs _
    change pairKernelExt38 g s 0 * coverRep38 (0 : PhysicalL2) s +
      pairKernelExt38 g s 1 * coverRep38 x s = _
    rw [hs]
    ring
  rw [h, star_star]

/-- The Hilbert gradient of an integral-defined functional is its kernel class. -/
theorem pairGradientCLM_integralPairCLM38 (g : PairKernelCont38) :
    pairGradientCLM (integralPairCLM38 g ⟨1, zero_le_one, le_rfl⟩) = pairKernelL2Class38 g :=
  Prod.ext (star_toDual_symm_integralPairCLM38_inl g) (star_toDual_symm_integralPairCLM38_inr g)

theorem pairGradientCLM_gradDiscrimCLM (φ : PotPair) (z : ℂ) :
    pairGradientCLM (gradDiscrimCLM φ z) = gradDiscrimL2 φ z :=
  pairGradientCLM_integralPairCLM38 (gradDiscrimCont38 φ z)

/-! ### M3: continuous linear maps commute with circle integrals -/

theorem clm_circleIntegral_comm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (S : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    S (circleIntegral f c R) = circleIntegral (fun z => S (f z)) c R := by
  unfold circleIntegral
  have hi := (circleIntegrable_iff R).1 hf
  rw [← S.intervalIntegral_comp_comm hi]
  congr 1
  funext θ
  exact S.map_smul _ _

end
end NlsGge.ThirdConsultation.G5017Support1
