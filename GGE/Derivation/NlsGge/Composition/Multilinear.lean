import NlsGge.Composition.Bilinear

/-!
# W03.03 (iteration): lifting `ℂ`-linear maps and multilinear evaluation on `A_w`

Source: `paper/v2.tex`, line 1452 ("by iteration, multilinear evaluation") and lines 1475-1477
(`B_k[r,…,r] ∈ A_w`).

* `liftCLM hw L` : a `ℂ`-linear bounded `L : E →L[ℂ] F` acts coefficientwise on the model
  `Model E = ℓ²(ℤ;E)`, commutes with synthesis and has norm `≤ ‖L‖`.
* `multCLM hw k` : the model `Model (X[×k]→L[ℝ] Y)` of `A_w`-valued `k`-multilinear coefficients
  acts continuously multilinearly `Model X × … × Model X → Model Y`, pointwise-multilinear
  evaluation on synthesized functions, with norm `≤ (prodConst hw)^k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open MeasureTheory AddCircle Complex

section Lift

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {w : ℤ → ℝ}

theorem summable_sq_lift (L : E →L[ℂ] F) (g : Model E) :
    Summable fun n => ‖L (g n)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((g.summable_sq).mul_left (‖L‖ ^ 2))
  calc ‖L (g n)‖ ^ 2 ≤ (‖L‖ * ‖g n‖) ^ 2 := by
        gcongr; exact L.le_opNorm _
    _ = ‖L‖ ^ 2 * ‖g n‖ ^ 2 := by ring

/-- Coefficientwise action of a `ℂ`-linear map on the model. -/
def liftModel (L : E →L[ℂ] F) (g : Model E) : Model F :=
  Model.mk (fun n => L (g n)) (summable_sq_lift L g)

@[simp] theorem liftModel_apply (L : E →L[ℂ] F) (g : Model E) (n : ℤ) :
    liftModel L g n = L (g n) := rfl

theorem norm_liftModel_le (L : E →L[ℂ] F) (g : Model E) : ‖liftModel L g‖ ≤ ‖L‖ * ‖g‖ := by
  refine Model.norm_le_of_tsum_le _ (by positivity) ?_
  calc ∑' n, ‖liftModel L g n‖ ^ 2 ≤ ∑' n, ‖L‖ ^ 2 * ‖g n‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq_lift L g)
          ((g.summable_sq).mul_left _)
        simp only [liftModel_apply]
        calc ‖L (g n)‖ ^ 2 ≤ (‖L‖ * ‖g n‖) ^ 2 := by gcongr; exact L.le_opNorm _
          _ = ‖L‖ ^ 2 * ‖g n‖ ^ 2 := by ring
    _ = ‖L‖ ^ 2 * ∑' n, ‖g n‖ ^ 2 := tsum_mul_left
    _ = (‖L‖ * ‖g‖) ^ 2 := by rw [mul_pow, g.norm_sq_eq]

/-- A bounded `ℂ`-linear map `E →L[ℂ] F` induces an `ℝ`-linear bounded map `Model E → Model F`
(coefficientwise), of norm `≤ ‖L‖`. -/
def liftCLM (_hw : AdmissibleWeight w) (L : E →L[ℂ] F) : Model E →L[ℝ] Model F :=
  LinearMap.mkContinuous
    { toFun := liftModel L
      map_add' := fun g h => Model.ext fun n => by simp
      map_smul' := fun c g => Model.ext fun n => by
        simp only [liftModel_apply, Model.smul_apply, RingHom.id_apply]
        exact (L.restrictScalars ℝ).map_smul c (g n) }
    ‖L‖ (fun g => norm_liftModel_le L g)

@[simp] theorem liftCLM_apply (hw : AdmissibleWeight w) (L : E →L[ℂ] F) (g : Model E) (n : ℤ) :
    liftCLM hw L g n = L (g n) := rfl

theorem norm_liftCLM_le (hw : AdmissibleWeight w) (L : E →L[ℂ] F) : ‖liftCLM hw L‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg L) _

theorem synth_liftCLM (hw : AdmissibleWeight w) (L : E →L[ℂ] F) (g : Model E)
    (θ : AddCircle (1 : ℝ)) : synth w (liftCLM hw L g) θ = L (synth w g θ) := by
  unfold synth expSum
  have hs := summable_expSum_terms (summable_norm_coeff hw g).1 θ
  rw [L.map_tsum hs]
  refine tsum_congr fun n => ?_
  simp only [coeff, liftCLM_apply, map_smul]
  congr 1
  exact ((L.restrictScalars ℝ).map_smul _ _).symm

end Lift

section Mult

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable {w : ℤ → ℝ}

/-- Evaluation of a `0`-multilinear map, as a `ℂ`-linear map of norm `≤ 1`. -/
def ev0 (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] :
    ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) Y →L[ℂ] Y :=
  LinearMap.mkContinuous
    { toFun := fun A => A 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun A => by
      have := (continuousMultilinearCurryFin0 ℝ X Y).norm_map A
      simp only [one_mul]
      exact this.le)

/-- The currying `L^{k+1} →L (X →L L^k)` (separation of the first variable). -/
def evSucc (k : ℕ) (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => X) Y →L[ℝ]
      X →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) Y).toLinearIsometry.toContinuousLinearMap

theorem evSucc_apply (k : ℕ) (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => X) Y) (x : X)
    (v : Fin k → X) : evSucc k X Y B x v = B (Fin.cons x v) := rfl

/-- `D:lem:composition` (iteration): the continuous `k`-multilinear evaluation on the model. -/
def multCLM (hw : AdmissibleWeight w) :
    (k : ℕ) → Model (ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Model X) (Model Y)
  | 0 => (continuousMultilinearCurryFin0 ℝ (Model X) (Model Y)).symm.toLinearIsometry.toContinuousLinearMap.comp
      (liftCLM hw (ev0 X Y))
  | k + 1 =>
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Model X)
      (Model Y)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ (Model X) _ _ (multCLM hw k)).comp
      (prodCLM hw (evSucc k X Y)))

theorem multCLM_succ_eq (hw : AdmissibleWeight w) (k : ℕ) :
    multCLM hw (k + 1) (X := X) (Y := Y) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Model X)
        (Model Y)).symm.toLinearIsometry.toContinuousLinearMap.comp
      ((ContinuousLinearMap.compL ℝ (Model X) _ _ (multCLM hw k)).comp
        (prodCLM hw (evSucc k X Y))) := rfl

theorem multCLM_zero_apply (hw : AdmissibleWeight w)
    (B : Model (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) Y)) (r : Fin 0 → Model X) :
    multCLM hw 0 B r = liftCLM hw (ev0 X Y) B := rfl

theorem multCLM_succ_apply (hw : AdmissibleWeight w) (k : ℕ)
    (B : Model (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => X) Y))
    (r : Fin (k + 1) → Model X) :
    multCLM hw (k + 1) B r = multCLM hw k (prodCLM hw (evSucc k X Y) B (r 0)) (Fin.tail r) := rfl

theorem synth_multCLM (hw : AdmissibleWeight w) (k : ℕ)
    (B : Model (ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y)) (r : Fin k → Model X)
    (θ : AddCircle (1 : ℝ)) :
    synth w (multCLM hw k B r) θ = synth w B θ (fun i => synth w (r i) θ) := by
  induction k with
  | zero =>
    rw [multCLM_zero_apply, synth_liftCLM]
    show synth w B θ 0 = _
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    rw [multCLM_succ_apply, ih, synth_prodCLM]
    show synth w B θ (Fin.cons (synth w (r 0) θ) fun i => synth w (Fin.tail r i) θ) = _
    congr 1
    funext i
    refine Fin.cases rfl (fun j => rfl) i

theorem norm_ev0_le (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] : ‖ev0 X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_prodCLM_evSucc_le (hw : AdmissibleWeight w) (k : ℕ) :
    ‖prodCLM hw (evSucc k X Y)‖ ≤ prodConst hw := by
  refine (norm_prodCLM_le hw _).trans ?_
  refine mul_le_of_le_one_right (prodConst_nonneg hw) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun B => ?_
  rw [one_mul]
  exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) Y).norm_map B).le

theorem norm_multCLM_le (hw : AdmissibleWeight w) (k : ℕ) :
    ‖multCLM hw k (X := X) (Y := Y)‖ ≤ (prodConst hw) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(continuousMultilinearCurryFin0 ℝ (Model X)
        (Model Y)).symm.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 :=
      LinearIsometry.norm_toContinuousLinearMap_le _
    have h2 : ‖liftCLM hw (ev0 X Y)‖ ≤ 1 := (norm_liftCLM_le hw _).trans (norm_ev0_le X Y)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  | succ k ih =>
    rw [multCLM_succ_eq]
    have hP := norm_prodCLM_evSucc_le hw k (X := X) (Y := Y)
    refine ContinuousLinearMap.opNorm_le_bound _ (by have := prodConst_nonneg hw; positivity)
      fun B => ?_
    rw [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
    show ‖(multCLM hw k (X := X) (Y := Y)).comp (prodCLM hw (evSucc k X Y) B)‖ ≤ _
    calc _ ≤ ‖multCLM hw k (X := X) (Y := Y)‖ * ‖prodCLM hw (evSucc k X Y) B‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ prodConst hw ^ k * (prodConst hw * ‖B‖) := by
          refine mul_le_mul ih ?_ (norm_nonneg _) (by have := prodConst_nonneg hw; positivity)
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
      _ = prodConst hw ^ (k + 1) * ‖B‖ := by ring

end Mult

end NlsGge.Composition
