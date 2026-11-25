import Mathlib
import NlsGge.Atomic.R.R025
import NlsGge.ThirdConsultation.R.RamerSetting06

                                                                                                 
                                                                                                      
                                                                                         
                                                                                                  
                                                                                                
                                                                                                           
                                                                                                               
                                                                                                                 
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The level-`N k + k` projection of a coordinate sample, embedded in `E_s`. -/
abbrev r026Proj {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ → ℕ) (k : ℕ) (z : ℤ → ℂ) : NlsGge.Pilot.FullWeightedHilbert c s :=
  NlsGge.Ramer.headToE c s (N k + k) (NlsGge.Ramer.headPt c (N k + k) z)

/-- Pointwise bound for the scalar product-rule error (real, outer norm). -/
theorem r026_div_pointwise {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (B p pR D dR : ℝ) (gP gR A G : W) (hp : ‖p‖ ≤ B) (hgP : ‖gP‖ ≤ B) :
    ‖p * D - inner ℝ gP A - (pR * dR - inner ℝ gR G)‖ ≤
      ‖B * ‖D - dR‖ + ‖p - pR‖ * ‖dR‖ + B * ‖A - G‖ + ‖gP - gR‖ * ‖G‖‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg p).trans hp
  have hnn : 0 ≤ B * ‖D - dR‖ + ‖p - pR‖ * ‖dR‖ + B * ‖A - G‖ + ‖gP - gR‖ * ‖G‖ :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg hB0 (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (mul_nonneg hB0 (norm_nonneg _)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Real.norm_of_nonneg hnn]
  have e : p * D - inner ℝ gP A - (pR * dR - inner ℝ gR G) =
      p * (D - dR) + (p - pR) * dR - inner ℝ gP (A - G) - inner ℝ (gP - gR) G := by
    rw [inner_sub_right, inner_sub_left]; ring
  rw [e]
  have t1 : ‖p * (D - dR)‖ ≤ B * ‖D - dR‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have t2 : ‖(p - pR) * dR‖ ≤ ‖p - pR‖ * ‖dR‖ := (norm_mul _ _).le
  have t3 : ‖inner ℝ gP (A - G)‖ ≤ B * ‖A - G‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hgP (norm_nonneg _))
  have t4 : ‖inner ℝ (gP - gR) G‖ ≤ ‖gP - gR‖ * ‖G‖ := norm_inner_le_norm _ _
  have s1 := norm_sub_le (p * (D - dR) + (p - pR) * dR - inner ℝ gP (A - G)) (inner ℝ (gP - gR) G)
  have s2 := norm_sub_le (p * (D - dR) + (p - pR) * dR) (inner ℝ gP (A - G))
  have s3 := norm_add_le (p * (D - dR)) ((p - pR) * dR)
  linarith

/-- Pointwise bound for the vector product-rule error (outer norm of the norm). -/
theorem r026_field_pointwise {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (B p pR : ℝ) (A G : W) (hp : ‖p‖ ≤ B) :
    ‖‖p • A - pR • G‖‖ ≤ ‖B * ‖A - G‖ + ‖p - pR‖ * ‖G‖‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg p).trans hp
  have hnn : 0 ≤ B * ‖A - G‖ + ‖p - pR‖ * ‖G‖ :=
    add_nonneg (mul_nonneg hB0 (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_norm, Real.norm_of_nonneg hnn]
  have e : p • A - pR • G = p • (A - G) + (p - pR) • G := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  have s := norm_add_le (p • (A - G)) ((p - pR) • G)
  have t1 : ‖p • (A - G)‖ ≤ B * ‖A - G‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have t2 : ‖(p - pR) • G‖ ≤ ‖p - pR‖ * ‖G‖ := (norm_smul _ _).le
  linarith

/-- Distance to a limit, for a continuous map of a convergent sequence. -/
theorem r026_norm_tendsto {X W : Type*} [NormedAddCommGroup W] [TopologicalSpace X]
    (f : X → W) (hf : Continuous f) {x : ℕ → X} {y : X}
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => ‖f (x k) - f y‖) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k => f (x k) - f y) atTop (𝓝 (f y - f y)) :=
    ((hf.tendsto y).comp hx).sub_const (f y)
  rw [sub_self] at h0
  exact tendsto_norm_zero.comp h0

/-- Two-sided bound of a difference by twice the bound. -/
theorem r026_sub_bound {W : Type*} [NormedAddCommGroup W] (x y : W) (M : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) : |‖x - y‖| ≤ 2 * M := by
  rw [abs_of_nonneg (norm_nonneg _)]
  linarith [norm_sub_le x y]

/-- The product of a bounded `C²` scalar with an `L²` core is an `L²` core at the larger level. -/
theorem r026_fieldMul_core {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (η : NlsGge.Pilot.FullWeightedHilbert c s → ℝ)
    (gradη : NlsGge.Pilot.FullWeightedHilbert c s → NlsGge.Ramer.ActualCM c) (B : ℝ)
    (hs0 : 0 ≤ s) (hP : NlsGge.Ramer.ProductRuleClass c s hs0 η gradη B)
    {N M : ℕ} (h : N ≤ M)
    (f : NlsGge.Ramer.actualCMHead c N → NlsGge.Ramer.actualCMHead c N)
    (hf : GaussianL2CylindricalCore c N f) :
    GaussianL2CylindricalCore c M (NlsGge.Ramer.fieldMul c s η h f) := by
  have hL := r021_lift_core c h f hf
  unfold GaussianL2CylindricalCore at hL
  obtain ⟨hLc, hLL, hLD⟩ := hL
  have hC : ContDiff ℝ 2 (NlsGge.Ramer.fieldMul c s η h f) :=
    NlsGge.Ramer.contDiff_fieldMul hP h f (r021_core_contDiff hf)
  have hφ : ContDiff ℝ 2
      (fun w : NlsGge.Ramer.actualCMHead c M => η (NlsGge.Ramer.headToE c s M w)) :=
    NlsGge.Ramer.contDiff_levelScalar hP M
  unfold GaussianL2CylindricalCore
  refine ⟨hC, ?_, ?_⟩
  · refine (hLL.norm.const_mul B).mono' hC.continuous.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    show ‖η (NlsGge.Ramer.headToE c s M v) • NlsGge.Ramer.liftField c h f v‖ ≤
      B * ‖NlsGge.Ramer.liftField c h f v‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hP.bound _) (norm_nonneg _)
  · refine ((hLD.norm.const_mul B).add (hLL.norm.const_mul B)).mono'
      (NlsGge.Ramer.continuous_finiteGaussianDivergence (hC.of_le (by norm_num))).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hφv : DifferentiableAt ℝ
        (fun w : NlsGge.Ramer.actualCMHead c M => η (NlsGge.Ramer.headToE c s M w)) v :=
      (hφ.differentiable (by norm_num)) v
    have hhv : DifferentiableAt ℝ (NlsGge.Ramer.liftField c h f) v :=
      (hLc.differentiable (by norm_num)) v
    have key : NlsGge.Ramer.finiteGaussianDivergence
        (fun y => η (NlsGge.Ramer.headToE c s M y) • NlsGge.Ramer.liftField c h f y) v =
        η (NlsGge.Ramer.headToE c s M v) *
            NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.liftField c h f) v -
          fderiv ℝ (fun w : NlsGge.Ramer.actualCMHead c M => η (NlsGge.Ramer.headToE c s M w)) v
            (NlsGge.Ramer.liftField c h f v) :=
      NlsGge.Ramer.finiteGaussianDivergence_smul
        (fun w : NlsGge.Ramer.actualCMHead c M => η (NlsGge.Ramer.headToE c s M w))
        (NlsGge.Ramer.liftField c h f) v hφv hhv
    show ‖NlsGge.Ramer.finiteGaussianDivergence
        (fun y => η (NlsGge.Ramer.headToE c s M y) • NlsGge.Ramer.liftField c h f y) v‖ ≤
      B * ‖NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.liftField c h f) v‖ +
        B * ‖NlsGge.Ramer.liftField c h f v‖
    rw [key]
    have h1 : ‖η (NlsGge.Ramer.headToE c s M v) *
        NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.liftField c h f) v‖ ≤
        B * ‖NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.liftField c h f) v‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hP.bound _) (norm_nonneg _)
    have h2 : ‖fderiv ℝ (fun w : NlsGge.Ramer.actualCMHead c M =>
        η (NlsGge.Ramer.headToE c s M w)) v (NlsGge.Ramer.liftField c h f v)‖ ≤
        B * ‖NlsGge.Ramer.liftField c h f v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (NlsGge.Ramer.norm_fderiv_levelScalar_le hP M v) (norm_nonneg _))
    have h3 := norm_sub_le (η (NlsGge.Ramer.headToE c s M v) *
        NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.liftField c h f) v)
        (fderiv ℝ (fun w : NlsGge.Ramer.actualCMHead c M =>
          η (NlsGge.Ramer.headToE c s M w)) v (NlsGge.Ramer.liftField c h f v))
    linarith

section ActualRamerSetting
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "γ" => NlsGge.Measure.fullWeightSequenceGaussian c.val
local notation "ρ" => NlsGge.Measure.fullWeightedSequenceRealization c s

/-- The Pro predicate gives the production product-rule structure, with the Riesz identity. -/
theorem r026_productClass (η : E → ℝ) (B : ℝ) (hc : ContDiff ℝ 2 η)
    (hB : ∀ x : E, ‖η x‖ ≤ B ∧ ‖hgrad c s hs η x‖ ≤ B) :
    NlsGge.Ramer.ProductRuleClass c s (le_of_lt (lt_trans (by norm_num) hs)) η
      (hgrad c s hs η) B := by
  refine ⟨hc, fun x => (hB x).1, fun x => (hB x).2, fun x h => ?_⟩
  unfold hgrad
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

/-- Pushforward of an `E_s`-valued `L²` quantity to the raw coordinate law. -/
theorem r026_push {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ = eLpNorm (fun z => F (ρ z)) 2 γ := by
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hmap : ramerGaussian c s = (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
      (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
  rw [hmap] at hF ⊢
  exact eLpNorm_map_measure hF hR.aemeasurable

/-- Membership in `L²` pulls back to the raw coordinate law. -/
theorem r026_memLp_push {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (hF : MemLp F 2 μ) :
    MemLp (fun z => F (ρ z)) 2 γ := by
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hmap : ramerGaussian c s = (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
      (NlsGge.Measure.fullWeightedSequenceRealization c s) := rfl
  rw [hmap] at hF
  exact (memLp_map_measure_iff hF.aestronglyMeasurable hR.aemeasurable).1 hF

/-- **R-026, closed-divergence product rule** (Pro round 6 head, verbatim). -/
theorem IsClosedDiv.smul
    (G : E → H) (d : E → ℝ) (η : E → ℝ)
    (hG : IsClosedDiv c s G d)
    (hη : ProductRuleClass c s hs η) :
    IsClosedDiv c s (fun x : E => η x • G x)
      (fun x : E => η x * d x - inner ℝ (hgrad c s hs η x) (G x)) := by
  have hs0 : (0 : ℝ) ≤ s := le_of_lt (lt_trans (by norm_num) hs)
  unfold ProductRuleClass at hη
  obtain ⟨hηC, B, hB⟩ := hη
  have hηc : Continuous η := hηC.continuous
  have hPC := r026_productClass c s hs η B hηC hB
  have hgc : Continuous (hgrad c s hs η) := hPC.continuous_grad
  have hR : Measurable (NlsGge.Measure.fullWeightedSequenceRealization c s) :=
    NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hcoord := r025_ae_coord c s hs
  unfold IsClosedDiv at hG ⊢
  obtain ⟨hGL, hdL, N, f, hf, hFd, hDd⟩ := hG
  have hGm : AEStronglyMeasurable G μ := hGL.aestronglyMeasurable
  have hdm : AEStronglyMeasurable d μ := hdL.aestronglyMeasurable
  have hηm : AEStronglyMeasurable η μ := hηc.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (hgrad c s hs η) μ := hgc.aestronglyMeasurable
  -- the two output fields are L²
  have hL1 : MemLp (fun x : E => η x • G x) 2 μ := by
    refine (hGL.norm.const_mul B).mono' (hηm.smul hGm) (Eventually.of_forall fun x => ?_)
    show ‖η x • G x‖ ≤ B * ‖G x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hB x).1 (norm_nonneg _)
  have hL2 : MemLp (fun x : E => η x * d x - inner ℝ (hgrad c s hs η x) (G x)) 2 μ := by
    refine ((hdL.norm.const_mul B).add (hGL.norm.const_mul B)).mono'
      ((hηm.mul hdm).sub (hgm.inner hGm)) (Eventually.of_forall fun x => ?_)
    show ‖η x * d x - inner ℝ (hgrad c s hs η x) (G x)‖ ≤ B * ‖d x‖ + B * ‖G x‖
    have h1 : ‖η x * d x‖ ≤ B * ‖d x‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB x).1 (norm_nonneg _)
    have h2 : ‖inner ℝ (hgrad c s hs η x) (G x)‖ ≤ B * ‖G x‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x).2 (norm_nonneg _))
    have h3 := norm_sub_le (η x * d x) (inner ℝ (hgrad c s hs η x) (G x))
    linarith
  -- the L² cores at level N k + k
  have hcore : ∀ k : ℕ, GaussianL2CylindricalCore c (N k + k)
      (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) :=
    fun k => r026_fieldMul_core c s η (hgrad c s hs η) B hs0 hPC (Nat.le_add_right (N k) k)
      (f k) (hf k)
  -- raw measurability and limits
  have hGr : MemLp (fun z => G (ρ z)) 2 γ := r026_memLp_push c s G hGL
  have hdr : MemLp (fun z => d (ρ z)) 2 γ := r026_memLp_push c s d hdL
  have hGnr : MemLp (fun z => ‖G (ρ z)‖) 2 γ := hGr.norm
  have hdnr : MemLp (fun z => ‖d (ρ z)‖) 2 γ := hdr.norm
  have hηρ : AEStronglyMeasurable (fun z => η (ρ z)) γ :=
    (hηc.measurable.comp hR).aestronglyMeasurable
  have hgρ : AEStronglyMeasurable (fun z => hgrad c s hs η (ρ z)) γ :=
    (hgc.comp_stronglyMeasurable hR.stronglyMeasurable).aestronglyMeasurable
  have hPae : ∀ᵐ z ∂γ, Tendsto (fun k : ℕ => r026Proj c s N k z) atTop (𝓝 (ρ z)) :=
    NlsGge.Ramer.ae_tendsto_headToE_level c s hs N
  have hPsm : ∀ k : ℕ, StronglyMeasurable (fun z : ℤ → ℂ => r026Proj c s N k z) := fun k =>
    (NlsGge.Ramer.headToE c s (N k + k)).continuous.comp_stronglyMeasurable
      (NlsGge.Ramer.measurable_headPt c (N k + k)).stronglyMeasurable
  have hPm : ∀ k : ℕ, Measurable (fun z : ℤ → ℂ => r026Proj c s N k z) := fun k =>
    (hPsm k).measurable
  have hηP : ∀ k : ℕ, AEStronglyMeasurable (fun z : ℤ → ℂ => η (r026Proj c s N k z)) γ :=
    fun k => (hηc.measurable.comp (hPm k)).aestronglyMeasurable
  have hgP : ∀ k : ℕ, AEStronglyMeasurable
      (fun z : ℤ → ℂ => hgrad c s hs η (r026Proj c s N k z)) γ :=
    fun k => (hgc.comp_stronglyMeasurable (hPsm k)).aestronglyMeasurable
  have hcylA : ∀ k : ℕ, AEStronglyMeasurable
      (fun z : ℤ → ℂ => NlsGge.Ramer.cylField c (N k) (f k) z) γ :=
    fun k => NlsGge.Ramer.aestronglyMeasurable_cylField c (f k)
      (r021_core_contDiff (hf k)).continuous
  have hcylD : ∀ k : ℕ, AEStronglyMeasurable
      (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (f k) z) γ :=
    fun k => NlsGge.Ramer.aestronglyMeasurable_cylDiv c (f k)
      ((r021_core_contDiff (hf k)).of_le (by norm_num))
  have hu0η : ∀ᵐ z ∂γ, Tendsto (fun k : ℕ => ‖η (r026Proj c s N k z) - η (ρ z)‖) atTop
      (𝓝 0) :=
    hPae.mono fun z hz => r026_norm_tendsto η hηc hz
  have hu0g : ∀ᵐ z ∂γ, Tendsto
      (fun k : ℕ => ‖hgrad c s hs η (r026Proj c s N k z) - hgrad c s hs η (ρ z)‖) atTop
      (𝓝 0) :=
    hPae.mono fun z hz => r026_norm_tendsto (hgrad c s hs η) hgc hz
  -- raw limits of the cylinders and divergences
  have hFr : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => NlsGge.Ramer.cylField c (N k) (f k) z - G (ρ z)) 2 γ) atTop (𝓝 0) := by
    refine hFd.congr (fun k => ?_)
    have hA : AEStronglyMeasurable (fun x : E => cylFieldE c s (N k) (f k) x - G x) μ :=
      (r021_aesm_cylFieldE c s (N k) (f k) (r021_core_contDiff (hf k)).continuous).sub hGm
    rw [r026_push c s _ hA]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoord] with z hz
    simp only [cylFieldE, hz]
  have hDr : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => NlsGge.Ramer.cylDiv c (N k) (f k) z - d (ρ z)) 2 γ) atTop (𝓝 0) := by
    refine hDd.congr (fun k => ?_)
    have hA : AEStronglyMeasurable (fun x : E => cylDivE c s (N k) (f k) x - d x) μ :=
      (r021_continuous_cylDivE c s (N k) (f k)
        ((r021_core_contDiff (hf k)).of_le (by norm_num))).aestronglyMeasurable.sub hdm
    rw [r026_push c s _ hA]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoord] with z hz
    simp only [cylDivE, hz]
  have hn1 : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => ‖NlsGge.Ramer.cylField c (N k) (f k) z - G (ρ z)‖) 2 γ) atTop (𝓝 0) :=
    hFr.congr (fun k => (eLpNorm_norm _ ((hcylA k).sub hGr.aestronglyMeasurable)).symm)
  have hn3 : Tendsto (fun k : ℕ => eLpNorm
      (fun z : ℤ → ℂ => ‖NlsGge.Ramer.cylDiv c (N k) (f k) z - d (ρ z)‖) 2 γ) atTop (𝓝 0) :=
    hDr.congr (fun k => (eLpNorm_norm _ ((hcylD k).sub hdr.aestronglyMeasurable)).symm)
  -- the field error on the raw law: squeeze, then the sum of two null sequences
  have hFieldRaw : Tendsto (fun k : ℕ => eLpNorm (fun z : ℤ → ℂ =>
      η (r026Proj c s N k z) • NlsGge.Ramer.cylField c (N k) (f k) z - η (ρ z) • G (ρ z)) 2 γ)
      atTop (𝓝 0) := by
    have hΦm : ∀ k : ℕ, AEStronglyMeasurable (fun z : ℤ → ℂ =>
        η (r026Proj c s N k z) • NlsGge.Ramer.cylField c (N k) (f k) z - η (ρ z) • G (ρ z)) γ :=
      fun k => ((hηP k).smul (hcylA k)).sub (hηρ.smul hGr.aestronglyMeasurable)
    have hnorm : Tendsto (fun k : ℕ => eLpNorm (fun z : ℤ → ℂ =>
        ‖η (r026Proj c s N k z) • NlsGge.Ramer.cylField c (N k) (f k) z - η (ρ z) • G (ρ z)‖)
        2 γ) atTop (𝓝 0) := by
      refine NlsGge.Ramer.tendsto_eLpNorm_zero_of_le
        (fun k z => ‖η (r026Proj c s N k z) • NlsGge.Ramer.cylField c (N k) (f k) z -
          η (ρ z) • G (ρ z)‖)
        (fun k z => B * ‖NlsGge.Ramer.cylField c (N k) (f k) z - G (ρ z)‖ +
          ‖η (r026Proj c s N k z) - η (ρ z)‖ * ‖G (ρ z)‖)
        (fun k => (hΦm k).norm)
        (fun k z => r026_field_pointwise B (η (r026Proj c s N k z))
          (η (ρ z)) (NlsGge.Ramer.cylField c (N k) (f k) z) (G (ρ z))
          (hB (r026Proj c s N k z)).1)
        ?_
      exact NlsGge.Ramer.tendsto_eLpNorm_zero_add _ _
        (NlsGge.Ramer.tendsto_eLpNorm_zero_const_mul B (fun k z => ‖NlsGge.Ramer.cylField c (N k) (f k) z -
          G (ρ z)‖) hn1)
        (NlsGge.Ramer.tendsto_eLpNorm_zero_of_bdd_mul (fun k z => ‖η (r026Proj c s N k z) - η (ρ z)‖)
          (fun k => ((hηP k).sub hηρ).norm) (2 * B)
          (fun k z => r026_sub_bound (η (r026Proj c s N k z)) (η (ρ z)) B
            (hB (r026Proj c s N k z)).1 (hB (ρ z)).1)
          hu0η (fun z => ‖G (ρ z)‖) hGnr)
    exact hnorm.congr (fun k => eLpNorm_norm _ (hΦm k))
  -- the divergence error on the raw law
  have hDivRaw : Tendsto (fun k : ℕ => eLpNorm (fun z : ℤ → ℂ =>
      η (r026Proj c s N k z) * NlsGge.Ramer.cylDiv c (N k) (f k) z -
        inner ℝ (hgrad c s hs η (r026Proj c s N k z)) (NlsGge.Ramer.cylField c (N k) (f k) z) -
        (η (ρ z) * d (ρ z) - inner ℝ (hgrad c s hs η (ρ z)) (G (ρ z)))) 2 γ) atTop (𝓝 0) := by
    have hΨm : ∀ k : ℕ, AEStronglyMeasurable (fun z : ℤ → ℂ =>
        η (r026Proj c s N k z) * NlsGge.Ramer.cylDiv c (N k) (f k) z -
          inner ℝ (hgrad c s hs η (r026Proj c s N k z)) (NlsGge.Ramer.cylField c (N k) (f k) z) -
          (η (ρ z) * d (ρ z) - inner ℝ (hgrad c s hs η (ρ z)) (G (ρ z)))) γ :=
      fun k => (((hηP k).mul (hcylD k)).sub ((hgP k).inner (hcylA k))).sub
        ((hηρ.mul hdr.aestronglyMeasurable).sub (hgρ.inner hGr.aestronglyMeasurable))
    have hb1 := NlsGge.Ramer.tendsto_eLpNorm_zero_const_mul B (fun k z => ‖NlsGge.Ramer.cylDiv c (N k) (f k) z -
      d (ρ z)‖) hn3
    have hb2 := NlsGge.Ramer.tendsto_eLpNorm_zero_of_bdd_mul (fun k z => ‖η (r026Proj c s N k z) - η (ρ z)‖)
      (fun k => ((hηP k).sub hηρ).norm) (2 * B)
      (fun k z => r026_sub_bound (η (r026Proj c s N k z)) (η (ρ z)) B
        (hB (r026Proj c s N k z)).1 (hB (ρ z)).1)
      hu0η (fun z => ‖d (ρ z)‖) hdnr
    have hb3 := NlsGge.Ramer.tendsto_eLpNorm_zero_const_mul B (fun k z =>
      ‖NlsGge.Ramer.cylField c (N k) (f k) z - G (ρ z)‖) hn1
    have hb4 := NlsGge.Ramer.tendsto_eLpNorm_zero_of_bdd_mul
      (fun k z => ‖hgrad c s hs η (r026Proj c s N k z) - hgrad c s hs η (ρ z)‖)
      (fun k => ((hgP k).sub hgρ).norm) (2 * B)
      (fun k z => r026_sub_bound (hgrad c s hs η (r026Proj c s N k z)) (hgrad c s hs η (ρ z)) B
        (hB (r026Proj c s N k z)).2 (hB (ρ z)).2)
      hu0g (fun z => ‖G (ρ z)‖) hGnr
    have s12 := NlsGge.Ramer.tendsto_eLpNorm_zero_add _ _ hb1 hb2
    have s123 := NlsGge.Ramer.tendsto_eLpNorm_zero_add _ _ s12 hb3
    have s1234 := NlsGge.Ramer.tendsto_eLpNorm_zero_add _ _ s123 hb4
    refine NlsGge.Ramer.tendsto_eLpNorm_zero_of_le
      (fun k z => η (r026Proj c s N k z) * NlsGge.Ramer.cylDiv c (N k) (f k) z -
        inner ℝ (hgrad c s hs η (r026Proj c s N k z)) (NlsGge.Ramer.cylField c (N k) (f k) z) -
        (η (ρ z) * d (ρ z) - inner ℝ (hgrad c s hs η (ρ z)) (G (ρ z))))
      (fun k z => B * ‖NlsGge.Ramer.cylDiv c (N k) (f k) z - d (ρ z)‖ +
        ‖η (r026Proj c s N k z) - η (ρ z)‖ * ‖d (ρ z)‖ +
        B * ‖NlsGge.Ramer.cylField c (N k) (f k) z - G (ρ z)‖ +
        ‖hgrad c s hs η (r026Proj c s N k z) - hgrad c s hs η (ρ z)‖ * ‖G (ρ z)‖)
      (fun k => hΨm k)
      (fun k z => r026_div_pointwise B (η (r026Proj c s N k z)) (η (ρ z))
        (NlsGge.Ramer.cylDiv c (N k) (f k) z) (d (ρ z))
        (hgrad c s hs η (r026Proj c s N k z)) (hgrad c s hs η (ρ z))
        (NlsGge.Ramer.cylField c (N k) (f k) z) (G (ρ z))
        (hB (r026Proj c s N k z)).1 (hB (r026Proj c s N k z)).2)
      s1234
  -- the field and divergence clauses on E_s, by pushing forward
  have hFieldE : Tendsto (fun k : ℕ => eLpNorm (fun x : E =>
      cylFieldE c s (N k + k) (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) x -
        η x • G x) 2 μ) atTop (𝓝 0) := by
    refine hFieldRaw.congr (fun k => ?_)
    have hC : ContDiff ℝ 2 (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) :=
      NlsGge.Ramer.contDiff_fieldMul hPC (Nat.le_add_right (N k) k) (f k) (r021_core_contDiff (hf k))
    have hA : AEStronglyMeasurable (fun x : E => cylFieldE c s (N k + k)
        (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) x - η x • G x) μ :=
      (r021_aesm_cylFieldE c s (N k + k)
        (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) hC.continuous).sub
        (hηm.smul hGm)
    rw [r026_push c s _ hA]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoord] with z hz
    simp only [cylFieldE, hz, NlsGge.Ramer.cylField_fieldMul]
  have hDivE : Tendsto (fun k : ℕ => eLpNorm (fun x : E =>
      cylDivE c s (N k + k) (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) x -
        (η x * d x - inner ℝ (hgrad c s hs η x) (G x))) 2 μ) atTop (𝓝 0) := by
    refine hDivRaw.congr (fun k => ?_)
    have hC : ContDiff ℝ 2 (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) :=
      NlsGge.Ramer.contDiff_fieldMul hPC (Nat.le_add_right (N k) k) (f k) (r021_core_contDiff (hf k))
    have hA : AEStronglyMeasurable (fun x : E => cylDivE c s (N k + k)
        (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k)) x -
          (η x * d x - inner ℝ (hgrad c s hs η x) (G x))) μ :=
      (r021_continuous_cylDivE c s (N k + k)
        (NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k))
        (hC.of_le (by norm_num))).aestronglyMeasurable.sub ((hηm.mul hdm).sub (hgm.inner hGm))
    rw [r026_push c s _ hA]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoord] with z hz
    simp only [cylDivE, hz, NlsGge.Ramer.cylDiv_fieldMul hPC (Nat.le_add_right (N k) k) (f k)
      (r021_core_contDiff (hf k))]
  exact ⟨hL1, hL2, fun k => N k + k,
    fun k => NlsGge.Ramer.fieldMul c s η (Nat.le_add_right (N k) k) (f k), hcore, hFieldE, hDivE⟩

end ActualRamerSetting

end
end NlsGge.ThirdConsultation.R
