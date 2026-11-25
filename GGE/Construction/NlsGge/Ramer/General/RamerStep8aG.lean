import Mathlib
import NlsGge.Ramer.General.FibreBridgeGb
import NlsGge.Ramer.General.RamerStep2FibrewiseG
import NlsGge.Ramer.General.RamerApproximantG
import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.RamerLemma52
import NlsGge.Ramer.RamerStep7

/-!
# R8a, generalized (GD6): the `S_P` identity (Ramer p.182) over a `RamerSetting S`

Adapted from `NlsGge/Ramer/RamerStep8a.lean`.  Dictionary: `inclE ↦ S.incl`,
`headProj c n ↦ S.headProj n`, `cmTrunc ↦ S.cmTrunc`, `headToE ↦ S.headToE`, `headCoord ↦
S.headCoordE`, `coordE ↦ S.coordE`, `realE ↦ S.R`, `fibreMapOf ↦ S.fibreMapOf`, `fibreJ ↦
S.fibreJ`, `ramerA ↦ S.ramerA`, `ramerJE ↦ S.ramerJE`, `hsDerivH ↦ S.hsDerivH`,
`fullWeightedSequenceGaussian ↦ S.γE`.  No norm of `E` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section Step8a

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Hypotheses of Ramer's Step 8: `Step7Hyp` for `L` and for every `P_n ∘ L`
(R6 on `B̄ = closedBall 0 ε`), and `L` is `C²`. -/
structure Step8Hyp (L : S.E → S.H) (ε : ℝ) : Prop where
  smooth : ContDiff ℝ 2 L
  step : Step7Hyp S.incl L ε
  stepP : ∀ n : ℕ, Step7Hyp S.incl (fun y => S.headProj n (L y)) ε

/-- `S_n y = y + i (P_n (L y))`. -/
def Sn (n : ℕ) (L : S.E → S.H) (y : S.E) : S.E :=
  y + S.incl (S.headProj n (L y))

theorem Sn_eq (n : ℕ) (L : S.E → S.H) (y : S.E) :
    S.Sn n L y = y + S.headToE n (S.cmTrunc n (L y)) := rfl

theorem continuous_Sn (n : ℕ) (L : S.E → S.H) (hL : Continuous L) :
    Continuous (S.Sn n L) := by
  unfold Sn
  exact continuous_id.add (S.incl.continuous.comp ((S.headProj n).continuous.comp hL))

theorem differentiable_Sn (n : ℕ) (L : S.E → S.H) (hL : Differentiable ℝ L) :
    Differentiable ℝ (S.Sn n L) := by
  unfold Sn
  exact differentiable_id.add (S.incl.differentiable.comp ((S.headProj n).differentiable.comp hL))

theorem sameTail_Sn (n : ℕ) (L : S.E → S.H) (x : S.E) : S.SameTail n (S.Sn n L x) x := by
  intro m hm
  rw [Sn, S.coord_add, S.coord_incl_headProj n _ m hm, add_zero]

variable (n : ℕ)

theorem headCoordE_tailBase_add (t : TailSpace n) (ht : S.TailSummable n t)
    (v : S.head n) :
    S.headCoordE n (S.tailBase n t + S.headToE n v) = v := by
  rw [← S.realE_headRec n v t ht, S.headCoordE_apply, S.coordE_realE _
    ((S.summable_headRec_iff n v t).2 ht), S.headPt_headRec]

theorem fibreMapOf_Sn (L : S.E → S.H)
    (t : TailSpace n) (ht : S.TailSummable n t) (v : S.head n) :
    S.fibreMapOf n (S.Sn n L) t v =
      v + S.cmTrunc n (L (S.tailBase n t + S.headToE n v)) := by
  rw [S.fibreMapOf_of_summable' n _ t ht]
  show S.headCoordE n (S.Sn n L _) = _
  rw [Sn_eq, map_add, S.headCoordE_headToE,
    S.headCoordE_tailBase_add n t ht]

/-- The fibre field `K_t v = P_n L (tailBase t + v)`. -/
def Kfib (L : S.E → S.H) (t : TailSpace n) (y : S.head n) : S.head n :=
  S.cmTrunc n (L (S.tailBase n t + S.headToE n y))

theorem tailSummable_coordE (x : S.E) :
    S.TailSummable n (tailPt n (S.coordE x)) := by
  have := (S.summable_headRec_iff n (S.headPt n (S.coordE x))
    (tailPt n (S.coordE x))).1
  rw [S.headRec_headPt_tailPt] at this
  exact this (S.memE_coordE x)

theorem tailBase_add_headToE (x : S.E) :
    S.tailBase n (tailPt n (S.coordE x)) +
      S.headToE n (S.headPt n (S.coordE x)) = x := by
  rw [← S.realE_headRec n _ _ (S.tailSummable_coordE n x), S.headRec_headPt_tailPt,
    S.realization_coordE]

theorem fibreMapOf_Sn_sub (L : S.E → S.H)
    (t : TailSpace n) (ht : S.TailSummable n t) :
    (fun y => S.fibreMapOf n (S.Sn n L) t y - y) = S.Kfib n L t := by
  funext y
  rw [S.fibreMapOf_Sn n L t ht, add_sub_cancel_left]
  rfl

theorem fderiv_Kfib (L : S.E → S.H) (hL : Differentiable ℝ L)
    (t : TailSpace n) (v : S.head n) :
    fderiv ℝ (S.Kfib n L t) v = (S.cmTrunc n).comp
      ((fderiv ℝ L (S.tailBase n t + S.headToE n v)).comp (S.headToE n)) := by
  have h1 : HasFDerivAt (fun y : S.head n => S.tailBase n t + S.headToE n y)
      (S.headToE n) v := (S.headToE n).hasFDerivAt.const_add _
  have h2 := (hL (S.tailBase n t + S.headToE n v)).hasFDerivAt.comp v h1
  exact ((S.cmTrunc n).hasFDerivAt.comp v h2).fderiv

theorem differentiable_Kfib (L : S.E → S.H) (hL : Differentiable ℝ L)
    (t : TailSpace n) : Differentiable ℝ (S.Kfib n L t) := by
  unfold Kfib
  exact (S.cmTrunc n).differentiable.comp (hL.comp
    (differentiable_const _ |>.add (S.headToE n).differentiable))

/-- Every fibre map of `S_n` is differentiable. -/
theorem differentiable_fibreMapOf_Sn
    (L : S.E → S.H) (hL : Differentiable ℝ L) (t : TailSpace n) :
    Differentiable ℝ (S.fibreMapOf n (S.Sn n L) t) := by
  by_cases ht : S.TailSummable n t
  · have : S.fibreMapOf n (S.Sn n L) t = fun y => y + S.Kfib n L t y := by
      funext y; rw [S.fibreMapOf_Sn n L t ht]; rfl
    rw [this]
    exact differentiable_id.add (S.differentiable_Kfib n L hL t)
  · rw [S.fibreMapOf_of_not_summable' n _ t ht]
    exact differentiable_id

/-! ### (iii) the norm -/

theorem norm_fibre_Sn (L : S.E → S.H) (x : S.E) :
    ‖S.fibreMapOf n (S.Sn n L) (tailPt n (S.coordE x)) (S.headPt n (S.coordE x)) -
        S.headPt n (S.coordE x)‖ = ‖S.headProj n (L x)‖ := by
  have := congrFun (S.fibreMapOf_Sn_sub n L _ (S.tailSummable_coordE n x))
    (S.headPt n (S.coordE x))
  rw [this]
  unfold Kfib
  rw [S.tailBase_add_headToE]
  rfl

/-! ### (ii) the divergence -/

theorem divergence_fibre_Sn (L : S.E → S.H)
    (hL : ContDiff ℝ 1 L) (x : S.E) :
    finiteGaussianDivergence (S.Kfib n L (tailPt n (S.coordE x)))
        (S.headPt n (S.coordE x)) =
      S.ramerA n L (S.coordE x) := by
  set z := S.coordE x with hz
  set t := tailPt n z with ht
  set v := S.headPt n z with hv
  set G : S.E → S.H := fun y => L (S.tailBase n t + y) with hG
  have hGd : ContDiff ℝ 1 G := hL.comp (contDiff_const.add contDiff_id)
  have hbase := S.tailBase_add_headToE n x
  have h := S.cylDiv_gRamer (le_refl n) G hGd z
  have hK : S.gRamer (le_refl n) G = S.Kfib n L t := by
    funext y
    apply Subtype.ext
    rfl
  rw [← hK]
  unfold cylDiv at h
  rw [h]
  unfold ramerA
  rw [S.realization_coordE]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e1 : G (S.headToE n v) = L x := by
    simp only [hG]; rw [hbase]
  have e2 : fderiv ℝ G (S.headToE n v) = fderiv ℝ L x := by
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := L) (x := S.headToE n v) (S.tailBase n t)
    exact this.trans (congrArg (fderiv ℝ L) hbase)
  rw [e1, e2]

/-! ### (i) the determinant -/

theorem det2_fibre_Sn (L : S.E → S.H)
    (hL : Differentiable ℝ L) (x : S.E) :
    NlsGge.Ramer.finiteDet2 (fderiv ℝ (S.Kfib n L (tailPt n (S.coordE x)))
        (S.headPt n (S.coordE x))) =
      det2 (S.hsDerivH (fun y => S.headProj n (L y)) x) := by
  set z := S.coordE x with hz
  set t := tailPt n z with ht
  set v := S.headPt n z with hv
  set B := S.hsDerivH (fun y => S.headProj n (L y)) x with hB
  have hbase := S.tailBase_add_headToE n x
  have hPL : DifferentiableAt ℝ (fun y => S.headProj n (L y)) x :=
    (S.headProj n).differentiableAt.comp x (hL x)
  have hDP : fderiv ℝ (fun y => S.headProj n (L y)) x = (S.headProj n).comp (fderiv ℝ L x) :=
    ((S.headProj n).hasFDerivAt.comp x (hL x).hasFDerivAt).fderiv
  have hBc : ∀ h, B.toCLM h = S.headProj n (fderiv ℝ L x (S.incl h)) := by
    intro h
    rw [hB, S.hsDerivH_toCLM, hDP]
    rfl
  have hV : LinearMap.range B.toCLM.toLinearMap ≤ S.head n := by
    rintro _ ⟨h, rfl⟩
    show B.toCLM h ∈ S.head n
    rw [hBc]
    exact (S.cmTrunc n _).2
  have hfr : HilbertSchmidt.HasFiniteRank B.toCLM := Submodule.finiteDimensional_of_le hV
  rw [det2_of_finiteRank B hfr, finiteRankDet2_eq_restriction _ hfr (S.head n) hV]
  have hrest : restrictedEnd B.toCLM.toLinearMap (S.head n) hV =
      ((fderiv ℝ (S.Kfib n L t) v : S.head n →L[ℝ] S.head n) :
        S.head n →ₗ[ℝ] S.head n) := by
    ext1 w
    apply Subtype.ext
    rw [S.fderiv_Kfib n L hL t v]
    show B.toCLM (w : S.H) = _
    rw [hBc]
    have : (S.incl (w : S.H)) = S.headToE n w := rfl
    rw [this]
    have hb : S.tailBase n t + S.headToE n v = x := hbase
    rw [hb]
    rfl
  rw [hrest]
  rfl

/-! ### The fibre Jacobian of `S_n` -/

/-- `J^{S_n}(x) = |det₂(P_n D_H L x)| exp(-a_n(x) - ½‖P_n L x‖²)`, as `ramerJE` of the field
`P_n ∘ L` with divergence `ramerA n L`. -/
def ramerJn (L : S.E → S.H) (x : S.E) : ℝ :=
  S.ramerJE (fun y => S.headProj n (L y)) (S.ramerA n L) x

theorem ramerJn_eq (L : S.E → S.H) (x : S.E) :
    S.ramerJn n L x =
      |det2 (S.hsDerivH (fun y => S.headProj n (L y)) x)| *
        Real.exp (-(S.ramerA n L (S.coordE x)) -
          ‖S.headProj n (L x)‖ ^ 2 / 2) :=
  S.ramerJE_eq _ _ x

/-- **R8a (i)-(iii) assembled**: the fibre Jacobian of `S_n` at `coordE x` is `J^{S_n}(x)`. -/
theorem fibreJ_Sn_eq (L : S.E → S.H)
    (hL : ContDiff ℝ 1 L) (x : S.E) :
    S.fibreJ n (S.fibreMapOf n (S.Sn n L)) (S.coordE x) = S.ramerJn n L x := by
  have hLd : Differentiable ℝ L := hL.differentiable one_ne_zero
  rw [S.fibreJ_eq_det2_form n _ (S.differentiable_fibreMapOf_Sn n L hLd) (S.coordE x),
    S.fibreMapOf_Sn_sub n L _ (S.tailSummable_coordE n x), ramerJn_eq,
    S.det2_fibre_Sn n L hLd x, S.divergence_fibre_Sn n L hL x]
  rw [S.norm_fibre_Sn n L x]

theorem measurable_fibreJ_Sn (L : S.E → S.H)
    (hL : ContDiff ℝ 1 L) :
    Measurable (S.fibreJ n (S.fibreMapOf n (S.Sn n L))) := by
  classical
  have hLd : Differentiable ℝ L := hL.differentiable one_ne_zero
  have hS := S.measurable_fibreMapOf n (S.Sn n L)
    (S.continuous_Sn n L hL.continuous).measurable
  have hset : MeasurableSet {z : ℤ → ℂ | S.TailSummable n (tailPt n z)} :=
    (S.measurableSet_tailSummable n).preimage (measurable_tailPt n)
  refine S.measurable_fibreJ_of_det n _ hS ?_
  have hDc : Continuous (fderiv ℝ L) := hL.continuous_fderiv one_ne_zero
  have hcont : Continuous (fun y : S.E =>
      (ContinuousLinearMap.id ℝ (S.head n) + (S.cmTrunc n).comp
        ((fderiv ℝ L y).comp (S.headToE n))).det) := by
    refine ContinuousLinearMap.continuous_det.comp ?_
    exact continuous_const.add (continuous_const.clm_comp (hDc.clm_comp continuous_const))
  have : (fun z : ℤ → ℂ =>
      (fderiv ℝ (S.fibreMapOf n (S.Sn n L) (tailPt n z)) (S.headPt n z)).det) =
      fun z => if S.TailSummable n (tailPt n z) then
        (ContinuousLinearMap.id ℝ (S.head n) + (S.cmTrunc n).comp
          ((fderiv ℝ (L) (S.R z)).comp (S.headToE n))).det else 1 := by
    funext z
    split_ifs with ht
    · have hb : S.tailBase n (tailPt n z) + S.headToE n (S.headPt n z) = S.R z := by
        rw [← S.realE_headRec n _ _ ht, S.headRec_headPt_tailPt]
      have e : S.fibreMapOf n (S.Sn n L) (tailPt n z) =
          fun y => y + S.Kfib n L (tailPt n z) y := by
        funext y; rw [S.fibreMapOf_Sn n L _ ht y]; rfl
      rw [e, fderiv_fun_add differentiableAt_fun_id
        ((S.differentiable_Kfib n L hLd _) _), S.fderiv_Kfib n L hLd, fderiv_fun_id, hb]
    · rw [S.fibreMapOf_of_not_summable' n _ _ ht]
      simp [ContinuousLinearMap.det]
  rw [this]
  exact Measurable.ite hset
    (hcont.measurable.comp S.measurable_R)
    measurable_const

/-! ### The identity -/

theorem step8a (L : S.E → S.H) {ε : ℝ}
    (hyp : S.Step8Hyp L ε) (F : S.E → ℝ) (hF : Measurable F) :
    ∫⁻ x in ball (0 : S.E) (ε / 2), ENNReal.ofReal (F x) ∂S.γE =
      ∫⁻ x in closedBall (0 : S.E) ε ∩ S.Sn n L ⁻¹' ball (0 : S.E) (ε / 2),
        ENNReal.ofReal (F (S.Sn n L x)) * ENNReal.ofReal (S.ramerJn n L x) ∂S.γE := by
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hLd : Differentiable ℝ L := hL1.differentiable one_ne_zero
  have hSc := S.continuous_Sn n L hL1.continuous
  have hP := hyp.stepP n
  set A : Set S.E :=
    closedBall (0 : S.E) ε ∩ S.Sn n L ⁻¹' ball (0 : S.E) (ε / 2) with hA
  have hAm : MeasurableSet A :=
    measurableSet_closedBall.inter (isOpen_ball.preimage hSc).measurableSet
  have himg : S.Sn n L '' A = ball (0 : S.E) (ε / 2) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := ball_subset_image_S S.incl (fun y => S.headProj n (L y))
        hP.pos hP.diff hP.small hP.contr hz
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      show S.Sn n L x ∈ ball (0 : S.E) (ε / 2)
      have : S.Sn n L x = z := hxz
      rw [this]; exact hz
  have hinj : Set.InjOn (S.Sn n L) A :=
    (injOn_add_image S.incl (fun y => S.headProj n (L y)) hP.diff hP.contr).mono
      Set.inter_subset_left
  have h := S.lintegral_image_eq_fibre n (S.Sn n L) hSc.measurable
    (S.sameTail_Sn n L) (S.measurable_fibreJ_Sn n L hL1) A hAm
    (by rw [himg]; exact measurableSet_ball) hinj
    (fun t v _ _ => S.differentiable_fibreMapOf_Sn n L hLd t v)
    (fun y => ENNReal.ofReal (F y)) hF.ennreal_ofReal
  rw [himg] at h
  rw [h]
  refine setLIntegral_congr_fun hAm (fun x _ => ?_)
  rw [S.fibreJ_Sn_eq n L hL1 x]

end Step8a

end NlsGge.Ramer.General.RamerSetting
