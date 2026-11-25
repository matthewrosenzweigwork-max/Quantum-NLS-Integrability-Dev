import Mathlib
import NlsGge.Ramer.FibreBridge
import NlsGge.Ramer.RamerStep2Fibrewise
import NlsGge.Ramer.RamerLemma52
import NlsGge.Ramer.RamerStep7
import NlsGge.Ramer.RamerApproximant
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.RamerDensity

/-!
# R8a: the `S_P` identity (Ramer p.182)

See `RamerStep8a.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

local notation "realE" => NlsGge.Measure.fullWeightedSequenceRealization

section Step8a

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The inclusion `i : H → E`. -/
abbrev inclE (hs : (1 : ℝ) / 2 < s) : ActualCM c →L[ℝ] FullWeightedHilbert c s :=
  cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)

/-- Hypotheses of Ramer's Step 8: `Step7Hyp` for `L` and for every `P_n ∘ L`
(R6 on `B̄ = closedBall 0 ε`), and `L` is `C²`. -/
structure Step8Hyp (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) (ε : ℝ) : Prop where
  smooth : ContDiff ℝ 2 L
  step : Step7Hyp (inclE c s hs) L ε
  stepP : ∀ n : ℕ, Step7Hyp (inclE c s hs) (fun y => headProj c n (L y)) ε

/-- `S_n y = y + i (P_n (L y))`. -/
def Sn (hs : (1 : ℝ) / 2 < s) (n : ℕ) (L : FullWeightedHilbert c s → ActualCM c)
    (y : FullWeightedHilbert c s) : FullWeightedHilbert c s :=
  y + inclE c s hs (headProj c n (L y))

theorem Sn_eq (hs : (1 : ℝ) / 2 < s) (n : ℕ) (L : FullWeightedHilbert c s → ActualCM c)
    (y : FullWeightedHilbert c s) :
    Sn c s hs n L y = y + headToE c s n (cmTrunc c n (L y)) := by
  rw [Sn, headToE_eq_cmToFull c s (zero_le_of_half_lt hs)]
  rfl

theorem continuous_Sn (hs : (1 : ℝ) / 2 < s) (n : ℕ) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : Continuous L) : Continuous (Sn c s hs n L) := by
  unfold Sn
  exact continuous_id.add ((inclE c s hs).continuous.comp ((headProj c n).continuous.comp hL))

theorem differentiable_Sn (hs : (1 : ℝ) / 2 < s) (n : ℕ) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : Differentiable ℝ L) : Differentiable ℝ (Sn c s hs n L) := by
  unfold Sn
  exact differentiable_id.add ((inclE c s hs).differentiable.comp ((headProj c n).differentiable.comp hL))

theorem sameTail_Sn (hs : (1 : ℝ) / 2 < s) (n : ℕ) (L : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : SameTail c s n (Sn c s hs n L x) x := by
  intro m hm
  rw [Sn, coordE_add, coordE_incl_headProj c s (zero_le_of_half_lt hs) n _ m hm, add_zero]

variable (n : ℕ)

theorem headCoord_tailBase_add (t : TailSpace n) (ht : TailSummable c s n t)
    (v : actualCMHead c n) :
    headCoord c s n (tailBase c s n t + headToE c s n v) = v := by
  rw [← realE_headRec c s n v t ht, headCoord_apply, coordE_realE c s _
    ((summable_headRec_iff c s n v t).2 ht), headPt_headRec]

theorem fibreMapOf_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (t : TailSpace n) (ht : TailSummable c s n t) (v : actualCMHead c n) :
    fibreMapOf c s n (Sn c s hs n L) t v =
      v + cmTrunc c n (L (tailBase c s n t + headToE c s n v)) := by
  rw [fibreMapOf_of_summable' c s n _ t ht]
  show headCoord c s n (Sn c s hs n L _) = _
  rw [Sn_eq, map_add, headCoord_headToE,
    headCoord_tailBase_add c s n t ht]

/-- The fibre field `K_t v = P_n L (tailBase t + v)`. -/
def Kfib (L : FullWeightedHilbert c s → ActualCM c) (t : TailSpace n) (y : actualCMHead c n) :
    actualCMHead c n :=
  cmTrunc c n (L (tailBase c s n t + headToE c s n y))

theorem tailSummable_coordE (x : FullWeightedHilbert c s) :
    TailSummable c s n (tailPt n (coordE c s x)) := by
  have := (summable_headRec_iff c s n (headPt c n (coordE c s x))
    (tailPt n (coordE c s x))).1
  rw [headRec_headPt_tailPt] at this
  exact this (weightedSquareSummable_coordE c s x)

theorem tailBase_add_headToE (x : FullWeightedHilbert c s) :
    tailBase c s n (tailPt n (coordE c s x)) +
      headToE c s n (headPt c n (coordE c s x)) = x := by
  rw [← realE_headRec c s n _ _ (tailSummable_coordE c s n x), headRec_headPt_tailPt,
    realization_coordE]

theorem fibreMapOf_Sn_sub (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (t : TailSpace n) (ht : TailSummable c s n t) :
    (fun y => fibreMapOf c s n (Sn c s hs n L) t y - y) = Kfib c s n L t := by
  funext y
  rw [fibreMapOf_Sn c s n hs L t ht, add_sub_cancel_left]
  rfl

theorem fderiv_Kfib (L : FullWeightedHilbert c s → ActualCM c) (hL : Differentiable ℝ L)
    (t : TailSpace n) (v : actualCMHead c n) :
    fderiv ℝ (Kfib c s n L t) v = (cmTrunc c n).comp
      ((fderiv ℝ L (tailBase c s n t + headToE c s n v)).comp (headToE c s n)) := by
  have h1 : HasFDerivAt (fun y : actualCMHead c n => tailBase c s n t + headToE c s n y)
      (headToE c s n) v := (headToE c s n).hasFDerivAt.const_add _
  have h2 := (hL (tailBase c s n t + headToE c s n v)).hasFDerivAt.comp v h1
  exact ((cmTrunc c n).hasFDerivAt.comp v h2).fderiv

theorem differentiable_Kfib (L : FullWeightedHilbert c s → ActualCM c) (hL : Differentiable ℝ L)
    (t : TailSpace n) : Differentiable ℝ (Kfib c s n L t) := by
  unfold Kfib
  exact (cmTrunc c n).differentiable.comp (hL.comp
    (differentiable_const _ |>.add (headToE c s n).differentiable))

/-- Every fibre map of `S_n` is differentiable. -/
theorem differentiable_fibreMapOf_Sn (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) (hL : Differentiable ℝ L) (t : TailSpace n) :
    Differentiable ℝ (fibreMapOf c s n (Sn c s hs n L) t) := by
  by_cases ht : TailSummable c s n t
  · have : fibreMapOf c s n (Sn c s hs n L) t = fun y => y + Kfib c s n L t y := by
      funext y; rw [fibreMapOf_Sn c s n hs L t ht]; rfl
    rw [this]
    exact differentiable_id.add (differentiable_Kfib c s n L hL t)
  · rw [fibreMapOf_of_not_summable' c s n _ t ht]
    exact differentiable_id

/-! ### (iii) the norm -/

theorem norm_fibre_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    ‖fibreMapOf c s n (Sn c s hs n L) (tailPt n (coordE c s x)) (headPt c n (coordE c s x)) -
        headPt c n (coordE c s x)‖ = ‖headProj c n (L x)‖ := by
  have := congrFun (fibreMapOf_Sn_sub c s n hs L _ (tailSummable_coordE c s n x))
    (headPt c n (coordE c s x))
  rw [this]
  unfold Kfib
  rw [tailBase_add_headToE]
  rfl

/-! ### (ii) the divergence -/

theorem divergence_fibre_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : ContDiff ℝ 1 L) (x : FullWeightedHilbert c s) :
    finiteGaussianDivergence (Kfib c s n L (tailPt n (coordE c s x)))
        (headPt c n (coordE c s x)) =
      ramerA c s (zero_le_of_half_lt hs) n L (coordE c s x) := by
  set z := coordE c s x with hz
  set t := tailPt n z with ht
  set v := headPt c n z with hv
  set G : FullWeightedHilbert c s → ActualCM c := fun y => L (tailBase c s n t + y) with hG
  have hGd : ContDiff ℝ 1 G := hL.comp (contDiff_const.add contDiff_id)
  have hbase := tailBase_add_headToE c s n x
  have h := cylDiv_gRamer c s (zero_le_of_half_lt hs) (le_refl n) G hGd z
  have hK : gRamer c s (le_refl n) G = Kfib c s n L t := by
    funext y
    apply Subtype.ext
    rfl
  rw [← hK]
  unfold cylDiv at h
  rw [h]
  unfold ramerA
  rw [realization_coordE]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e1 : G (headToE c s n v) = L x := by
    simp only [hG]; rw [hbase]
  have e2 : fderiv ℝ G (headToE c s n v) = fderiv ℝ L x := by
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := L) (x := headToE c s n v) (tailBase c s n t)
    exact this.trans (congrArg (fderiv ℝ L) hbase)
  rw [e1, e2]

/-! ### (i) the determinant -/

theorem det2_fibre_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : Differentiable ℝ L) (x : FullWeightedHilbert c s) :
    NlsGge.Ramer.finiteDet2 (fderiv ℝ (Kfib c s n L (tailPt n (coordE c s x)))
        (headPt c n (coordE c s x))) =
      det2 (hsDerivH c s hs (fun y => headProj c n (L y)) x) := by
  set z := coordE c s x with hz
  set t := tailPt n z with ht
  set v := headPt c n z with hv
  set B := hsDerivH c s hs (fun y => headProj c n (L y)) x with hB
  have hbase := tailBase_add_headToE c s n x
  have hPL : DifferentiableAt ℝ (fun y => headProj c n (L y)) x :=
    (headProj c n).differentiableAt.comp x (hL x)
  have hDP : fderiv ℝ (fun y => headProj c n (L y)) x = (headProj c n).comp (fderiv ℝ L x) :=
    ((headProj c n).hasFDerivAt.comp x (hL x).hasFDerivAt).fderiv
  have hBc : ∀ h, B.toCLM h = headProj c n (fderiv ℝ L x
      (inclE c s hs h)) := by
    intro h
    rw [hB, hsDerivH_toCLM, hDP]
    rfl
  have hV : LinearMap.range B.toCLM.toLinearMap ≤ actualCMHead c n := by
    rintro _ ⟨h, rfl⟩
    show B.toCLM h ∈ actualCMHead c n
    rw [hBc]
    exact (cmTrunc c n _).2
  have hfr : HilbertSchmidt.HasFiniteRank B.toCLM := Submodule.finiteDimensional_of_le hV
  rw [det2_of_finiteRank B hfr, finiteRankDet2_eq_restriction _ hfr (actualCMHead c n) hV]
  have hrest : restrictedEnd B.toCLM.toLinearMap (actualCMHead c n) hV =
      ((fderiv ℝ (Kfib c s n L t) v : actualCMHead c n →L[ℝ] actualCMHead c n) :
        actualCMHead c n →ₗ[ℝ] actualCMHead c n) := by
    ext1 w
    apply Subtype.ext
    rw [fderiv_Kfib c s n L hL t v]
    show B.toCLM (w : ActualCM c) = _
    rw [hBc]
    have : (inclE c s hs (w : ActualCM c)) = headToE c s n w :=
      (headToE_eq_cmToFull c s (zero_le_of_half_lt hs) n w).symm
    rw [this]
    have hb : tailBase c s n t + headToE c s n v = x := hbase
    rw [hb]
    rfl
  rw [hrest]
  rfl

/-! ### The fibre Jacobian of `S_n` -/

/-- `J^{S_n}(x) = |det₂(P_n D_H L x)| exp(-a_n(x) - ½‖P_n L x‖²)`, as `ramerJE` of the field
`P_n ∘ L` with divergence `ramerA n L`. -/
def ramerJn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : ℝ :=
  ramerJE c s hs (fun y => headProj c n (L y)) (ramerA c s (zero_le_of_half_lt hs) n L) x

theorem ramerJn_eq (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    ramerJn c s n hs L x =
      |det2 (hsDerivH c s hs (fun y => headProj c n (L y)) x)| *
        Real.exp (-(ramerA c s (zero_le_of_half_lt hs) n L (coordE c s x)) -
          ‖headProj c n (L x)‖ ^ 2 / 2) :=
  ramerJE_eq c s hs _ _ x

/-- **R8a (i)-(iii) assembled**: the fibre Jacobian of `S_n` at `coordE x` is `J^{S_n}(x)`. -/
theorem fibreJ_Sn_eq (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : ContDiff ℝ 1 L) (x : FullWeightedHilbert c s) :
    fibreJ c n (fibreMapOf c s n (Sn c s hs n L)) (coordE c s x) = ramerJn c s n hs L x := by
  have hLd : Differentiable ℝ L := hL.differentiable one_ne_zero
  rw [fibreJ_eq_det2_form c n _ (differentiable_fibreMapOf_Sn c s n hs L hLd) (coordE c s x),
    fibreMapOf_Sn_sub c s n hs L _ (tailSummable_coordE c s n x), ramerJn_eq,
    det2_fibre_Sn c s n hs L hLd x, divergence_fibre_Sn c s n hs L hL x]
  rw [norm_fibre_Sn c s n hs L x]

theorem measurable_fibreJ_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : ContDiff ℝ 1 L) :
    Measurable (fibreJ c n (fibreMapOf c s n (Sn c s hs n L))) := by
  classical
  have hLd : Differentiable ℝ L := hL.differentiable one_ne_zero
  have hS := measurable_fibreMapOf c s n (Sn c s hs n L)
    (continuous_Sn c s hs n L hL.continuous).measurable
  have hset : MeasurableSet {z : ℤ → ℂ | TailSummable c s n (tailPt n z)} :=
    (measurableSet_tailSummable c s n).preimage (measurable_tailPt n)
  refine measurable_fibreJ_of_det c n _ hS ?_
  have hDc : Continuous (fderiv ℝ L) := hL.continuous_fderiv one_ne_zero
  have hcont : Continuous (fun y : FullWeightedHilbert c s =>
      (ContinuousLinearMap.id ℝ (actualCMHead c n) + (cmTrunc c n).comp
        ((fderiv ℝ L y).comp (headToE c s n))).det) := by
    refine ContinuousLinearMap.continuous_det.comp ?_
    exact continuous_const.add (continuous_const.clm_comp (hDc.clm_comp continuous_const))
  have : (fun z : ℤ → ℂ =>
      (fderiv ℝ (fibreMapOf c s n (Sn c s hs n L) (tailPt n z)) (headPt c n z)).det) =
      fun z => if TailSummable c s n (tailPt n z) then
        (ContinuousLinearMap.id ℝ (actualCMHead c n) + (cmTrunc c n).comp
          ((fderiv ℝ (L) (realE c s z)).comp (headToE c s n))).det else 1 := by
    funext z
    split_ifs with ht
    · have hb : tailBase c s n (tailPt n z) + headToE c s n (headPt c n z) = realE c s z := by
        rw [← realE_headRec c s n _ _ ht, headRec_headPt_tailPt]
      have e : fibreMapOf c s n (Sn c s hs n L) (tailPt n z) =
          fun y => y + Kfib c s n L (tailPt n z) y := by
        funext y; rw [fibreMapOf_Sn c s n hs L _ ht y]; rfl
      rw [e, fderiv_fun_add differentiableAt_fun_id
        ((differentiable_Kfib c s n L hLd _) _), fderiv_Kfib c s n L hLd, fderiv_fun_id, hb]
    · rw [fibreMapOf_of_not_summable' c s n _ _ ht]
      simp [ContinuousLinearMap.det]
  rw [this]
  exact Measurable.ite hset
    (hcont.measurable.comp (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s))
    measurable_const

/-! ### The identity -/

theorem step8a (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) (F : FullWeightedHilbert c s → ℝ) (hF : Measurable F) :
    ∫⁻ x in ball (0 : FullWeightedHilbert c s) (ε / 2), ENNReal.ofReal (F x)
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩ Sn c s hs n L ⁻¹'
          ball (0 : FullWeightedHilbert c s) (ε / 2),
        ENNReal.ofReal (F (Sn c s hs n L x)) * ENNReal.ofReal (ramerJn c s n hs L x)
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hLd : Differentiable ℝ L := hL1.differentiable one_ne_zero
  have hSc := continuous_Sn c s hs n L hL1.continuous
  have hP := hyp.stepP n
  set A : Set (FullWeightedHilbert c s) :=
    closedBall (0 : FullWeightedHilbert c s) ε ∩ Sn c s hs n L ⁻¹'
      ball (0 : FullWeightedHilbert c s) (ε / 2) with hA
  have hAm : MeasurableSet A :=
    measurableSet_closedBall.inter (isOpen_ball.preimage hSc).measurableSet
  have himg : Sn c s hs n L '' A = ball (0 : FullWeightedHilbert c s) (ε / 2) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := ball_subset_image_S (inclE c s hs) (fun y => headProj c n (L y))
        hP.pos hP.diff hP.small hP.contr hz
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      show Sn c s hs n L x ∈ ball (0 : FullWeightedHilbert c s) (ε / 2)
      have : Sn c s hs n L x = z := hxz
      rw [this]; exact hz
  have hinj : Set.InjOn (Sn c s hs n L) A :=
    (injOn_add_image (inclE c s hs) (fun y => headProj c n (L y)) hP.diff hP.contr).mono
      Set.inter_subset_left
  have h := lintegral_image_eq_fibre c s n hs (Sn c s hs n L) hSc.measurable
    (sameTail_Sn c s hs n L) (measurable_fibreJ_Sn c s n hs L hL1) A hAm
    (by rw [himg]; exact measurableSet_ball) hinj
    (fun t v _ _ => differentiable_fibreMapOf_Sn c s n hs L hLd t v)
    (fun y => ENNReal.ofReal (F y)) hF.ennreal_ofReal
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun hAm (fun x _ => ?_)
  rw [fibreJ_Sn_eq c s n hs L hL1 x]

end Step8a

end NlsGge.Ramer
