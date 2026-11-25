import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationA
import NlsGge.Birkhoff.F05Identity38

/-! # Analyticity of the actual finite-plane NLS Hamiltonian

The Hamiltonian `HΛ` is the literal physical Q₂ energy defined in `FlowRotationA`.
This module proves its real analyticity by finite-coordinate insertion, the
actual analytic inverse Birkhoff map, the reflected Fourier isometry, and the
quadratic and quartic carrier energy formulas.
-/

set_option autoImplicit false

noncomputable section

namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

/-- Finite-coordinate insertion into h¹, as a real continuous linear map. -/
private def finitePlaneH1_38 (Λ : Finset ℤ) :
    (Λ → ℂ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => carrierMk38 _ (extZero38 Λ w)
        (finiteSupport_mem_seqSobolev38 _ _ (finite_support_extZero38 Λ w))
      map_add' := by
        intro w v
        apply carrierExt38
        funext n
        change extZero38 Λ (w + v) n = extZero38 Λ w n + extZero38 Λ v n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn,
            extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            extZero38_apply_of_not_mem _ hn, add_zero]
      map_smul' := by
        intro c w
        apply carrierExt38
        funext n
        change extZero38 Λ (c • w) n = c • extZero38 Λ w n
        by_cases hn : n ∈ Λ
        · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn]
          rfl
        · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn,
            smul_zero] }

/-- The squared norm on a real inner product space is a continuous quadratic
polynomial and hence real analytic, including at zero. -/
private theorem analyticAt_normSq38 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) :
    AnalyticAt ℝ (fun y : E => ‖y‖ ^ 2) x := by
  have he : (fun y : E => ‖y‖ ^ 2) = fun y : E => innerSL ℝ y y := by
    funext y
    calc
      ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = innerSL ℝ y y := (innerSL_apply_apply ℝ y y).symm
  rw [he]
  exact ((innerSL ℝ (E := E)).analyticAt_bilinear (x, x)).comp
    (f := fun y : E => (y, y)) (analyticAt_id.prod analyticAt_id)

/-- On h¹, the full NLS Hamiltonian is real analytic: the kinetic term is a
quadratic polynomial and the quartic term is the norm square of convolution. -/
private theorem analyticAt_ham_coe38 (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    AnalyticAt ℝ (fun y : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
      ham (carrierCoe38 _ y)) x := by
  have hn := analyticAt_normSq38 x
  have hi := (analyticAt_normSq38 (incl01 x)).comp (incl01.analyticAt x)
  have hc : AnalyticAt ℝ (fun y => convC38 y y) x :=
    (convC38.analyticAt_bilinear (x, x)).comp
      (f := fun y : SobolevCarrier38 ((1 : ℕ) : ℝ) => (y, y))
      (analyticAt_id.prod analyticAt_id)
  have hq := (analyticAt_normSq38 (convC38 x x)).comp
    (f := fun y : SobolevCarrier38 ((1 : ℕ) : ℝ) => convC38 y y) hc
  simp only [ham_def, kin_coe_eq, quart_coe_eq]
  exact (analyticAt_const.mul (hn.sub hi)).add hq

/-- The literal physical finite-plane energy equals the carrier expression
obtained from the actual inverse and the reflected Fourier isometry. -/
private theorem HΛ_eq_carrier38 (Λ : Finset ℤ) (w : Λ → ℂ) :
    HΛ Λ w = ham (carrierCoe38 ((1 : ℕ) : ℝ)
      ((reflIso38 ((1 : ℕ) : ℝ)) ((B0).TinvC 1 (finitePlaneH1_38 Λ w)))) := by
  unfold HΛ
  congr 1
  have heq : fourierSeq38 ((B0).finiteGapField38 Λ w) =
      (B0).Tinv (extZero38 Λ w) := by
    rw [BirkhoffTop38.finiteGapField38,
      (B0).cleanΦinv_of_mem _ (extZero38_mem_zero Λ w), (B0).fourierSeq38_Φinv]
  funext n
  change physicalFourier ((B0).finiteGapField38 Λ w) n =
    -carrierCoe38 ((1 : ℕ) : ℝ) ((B0).TinvC 1 (finitePlaneH1_38 Λ w)) (-n)
  rw [BirkhoffTop38.TinvC_coe]
  change physicalFourier ((B0).finiteGapField38 Λ w) n = -(B0).Tinv (extZero38 Λ w) (-n)
  have hn := congrFun heq (-n)
  rw [fourierSeq38_apply, neg_neg] at hn
  simpa only [neg_neg] using congrArg Neg.neg hn

/-- For every finite set of integer modes, the literal finite-plane physical
NLS Hamiltonian HΛ is real analytic on a neighborhood of every finite-plane
point, with no exclusion of zero coordinates. -/
theorem analytic_HLambda38 (Λ : Finset ℤ) : AnalyticOnNhd ℝ (HΛ Λ) Set.univ := by
  intro w _
  rw [show HΛ Λ = fun v => ham (carrierCoe38 ((1 : ℕ) : ℝ)
      ((reflIso38 ((1 : ℕ) : ℝ)) ((B0).TinvC 1 (finitePlaneH1_38 Λ v)))) from
    funext (HΛ_eq_carrier38 Λ)]
  have hz := (finitePlaneH1_38 Λ).analyticAt w
  have ht := (NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.analyticOnNhd_TinvC
    1 _ (Set.mem_univ _)).comp hz
  have hr := ((reflIso38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt
    _).comp ht
  exact (analyticAt_ham_coe38 _).comp hr

end LiebLiniger.FixedPeriod.EXT
