import QuantumNLS.ProductTorusComplexification
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Analytic.Basic

/-!
# R-4C2E4AC7, stage C2 (Terra r167 item (c), part 2): complexification of continuous real multilinear maps

Source: `chapters/global/product_torus.tex`, theorem, lines 39–41 ("holomorphic extensions in the complexified initial
variable"); see the stage C1 module `ProductTorusComplexification` for the complexification `Cx F = F ⊕ i F`.

For a real inner product space `F` and the complex normed space `Cx F` of stage C1:
* `cxLin`: a real-linear `A : F →L[ℝ] W` into a complex normed space extends to the complex-linear
  `Ã z = A (re z) + i A (im z)`, with `‖Ã‖ ≤ 2 ‖A‖` (`norm_cxLin_le`);
* `cxML F n`: the complexification of continuous real `n`-linear maps `F^n → F` to continuous complex `n`-linear
  maps `(Cx F)^n → Cx F`, by currying: `q₀ = ι ∘ p₀`, `q_{n+1} = uncurry (complexify (a ↦ q_n (p.curryLeft a)))`.
  It is real-linear and bounded with `‖cxML F n‖ ≤ 2ⁿ` (`norm_cxML_le`), so `‖q_n‖ ≤ 2ⁿ ‖p_n‖`
  (`norm_cxML_apply_le`), and it agrees with `p` at real points: `q_n (ι a₁, …, ι aₙ) = ι (p_n (a₁, …, aₙ))`
  (`cxML_ι`);
* `cxSeries`: the termwise complexification of a real formal multilinear series, with `‖q n‖ ≤ 2ⁿ ‖p n‖`
  (`norm_cxSeries_le`) and `q n (ι y, …, ι y) = ι (p n (y, …, y))` (`cxSeries_ι`);
* `ιL`: the real embedding `ι` as a continuous real-linear map.
-/

set_option autoImplicit false

noncomputable section

namespace QuantumNLS.ProductTorusComplexMultilinear

open QuantumNLS.ProductTorusComplexification

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem norm_re_le (z : Cx F) : ‖Cx.re z‖ ≤ ‖z‖ := by
  have h := Cx.norm_sq z
  nlinarith [norm_nonneg z, norm_nonneg (Cx.re z), sq_nonneg ‖Cx.im z‖]

theorem norm_im_le (z : Cx F) : ‖Cx.im z‖ ≤ ‖z‖ := by
  have h := Cx.norm_sq z
  nlinarith [norm_nonneg z, norm_nonneg (Cx.im z), sq_nonneg ‖Cx.re z‖]

theorem ι_sub (a b : F) : Cx.ι (a - b) = Cx.ι a - Cx.ι b := Cx.ext (by simp) (by simp)

theorem ι_zero : Cx.ι (0 : F) = 0 := Cx.ext (by simp) (by simp)

/-- The real embedding as a continuous real-linear map (`Cx F` is real through `NormedSpace.complexToReal`). -/
def ιL : F →L[ℝ] Cx F :=
  LinearMap.mkContinuous
    { toFun := Cx.ι
      map_add' := Cx.ι_add
      map_smul' := fun c a => Cx.ι_smul c a }
    1 (fun a => by
      show ‖Cx.ι a‖ ≤ 1 * ‖a‖
      rw [Cx.norm_ι, one_mul])

@[simp] theorem ιL_apply (a : F) : (ιL : F →L[ℝ] Cx F) a = Cx.ι a := rfl

section Lin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]

theorem ofReal_smul' (x : ℝ) (w : W) : (x : ℂ) • w = x • w := by
  show (algebraMap ℝ ℂ x) • w = x • w
  exact algebraMap_smul ℂ x w

omit [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W] in
theorem I_smul_I_smul (w : W) : Complex.I • Complex.I • w = -w := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- Complexification of a continuous real-linear map `A : F →L[ℝ] W` into a complex normed space:
`Ã z = A (re z) + i A (im z)`. -/
def cxLin (A : F →L[ℝ] W) : Cx F →L[ℂ] W :=
  LinearMap.mkContinuous
    { toFun := fun z => A (Cx.re z) + Complex.I • A (Cx.im z)
      map_add' := fun z w => by
        simp only [Cx.re_add, Cx.im_add, map_add, smul_add]
        abel
      map_smul' := fun c z => by
        simp only [Cx.re_smul, Cx.im_smul, map_sub, map_add, map_smul, RingHom.id_apply]
        rw [← ofReal_smul' c.re (A (Cx.re z)), ← ofReal_smul' c.im (A (Cx.im z)),
          ← ofReal_smul' c.re (A (Cx.im z)), ← ofReal_smul' c.im (A (Cx.re z))]
        conv_rhs => rw [← Complex.re_add_im c]
        simp only [add_smul, smul_add, mul_smul, I_smul_I_smul, smul_neg]
        rw [smul_comm Complex.I (c.re : ℂ), smul_comm Complex.I (c.im : ℂ)]
        abel }
    (2 * ‖A‖) (fun z => by
      show ‖A (Cx.re z) + Complex.I • A (Cx.im z)‖ ≤ 2 * ‖A‖ * ‖z‖
      calc ‖A (Cx.re z) + Complex.I • A (Cx.im z)‖
          ≤ ‖A (Cx.re z)‖ + ‖Complex.I • A (Cx.im z)‖ := norm_add_le _ _
        _ = ‖A (Cx.re z)‖ + ‖A (Cx.im z)‖ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ ‖A‖ * ‖Cx.re z‖ + ‖A‖ * ‖Cx.im z‖ := add_le_add (A.le_opNorm _) (A.le_opNorm _)
        _ ≤ 2 * ‖A‖ * ‖z‖ := by
          nlinarith [norm_re_le z, norm_im_le z, norm_nonneg A, norm_nonneg z])

theorem cxLin_apply (A : F →L[ℝ] W) (z : Cx F) : cxLin A z = A (Cx.re z) + Complex.I • A (Cx.im z) := rfl

theorem norm_cxLin_le (A : F →L[ℝ] W) : ‖cxLin A‖ ≤ 2 * ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end Lin

theorem curryLeft_add_apply {n : ℕ} (p q : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) F) (x : F) :
    (p + q).curryLeft x = p.curryLeft x + q.curryLeft x := by
  ext m
  simp

theorem curryLeft_smul_apply {n : ℕ} (c : ℝ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) F)
    (x : F) : (c • p).curryLeft x = c • p.curryLeft x := by
  ext m
  simp

variable (F) in
/-- **Complexification of continuous real multilinear maps** `F^n → F`, by currying. -/
def cxML : (n : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => F) F →L[ℝ]
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Cx F) (Cx F)
  | 0 => LinearMap.mkContinuous
      { toFun := fun p => ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0))
        map_add' := fun p q => by
          ext v
          simp [Cx.ι_add]
        map_smul' := fun c p => by
          ext v
          simp [Cx.ι_smul] }
      1 (fun p => by
        show ‖ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0))‖ ≤ 1 * ‖p‖
        rw [ContinuousMultilinearMap.norm_constOfIsEmpty, Cx.norm_ι, one_mul]
        exact (p.le_opNorm 0).trans (by simp))
  | n + 1 => LinearMap.mkContinuous
      { toFun := fun p => (cxLin ((cxML n).comp p.curryLeft)).uncurryLeft
        map_add' := fun p q => by
          ext v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_add_apply, map_add, _root_.add_apply, smul_add]
          abel
        map_smul' := fun c p => by
          ext v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_smul_apply, map_smul, _root_.smul_apply, RingHom.id_apply]
          rw [smul_comm Complex.I c]
          rw [← smul_add]; rfl }
      (2 * ‖cxML n‖) (fun p => by
        refine (ContinuousLinearMap.uncurryLeft_norm (Ei := fun _ : Fin (n + 1) => Cx F)
          (cxLin ((cxML n).comp p.curryLeft))).le.trans ?_
        calc ‖cxLin ((cxML n).comp p.curryLeft)‖ ≤ 2 * ‖(cxML n).comp p.curryLeft‖ := norm_cxLin_le _
          _ ≤ 2 * (‖cxML n‖ * ‖p.curryLeft‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
          _ = 2 * ‖cxML n‖ * ‖p‖ := by rw [ContinuousMultilinearMap.curryLeft_norm, mul_assoc])

theorem cxML_zero_eq (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) F) :
    cxML F 0 p = ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (Cx.ι (p 0)) := by
  rfl

theorem cxML_succ_eq {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) F) :
    cxML F (n + 1) p = (cxLin ((cxML F n).comp p.curryLeft)).uncurryLeft := by
  rfl

theorem cxML_zero_apply (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) F) (v : Fin 0 → Cx F) :
    cxML F 0 p v = Cx.ι (p 0) := by
  rw [cxML_zero_eq, ContinuousMultilinearMap.constOfIsEmpty_apply]

theorem cxML_succ_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) F)
    (v : Fin (n + 1) → Cx F) :
    cxML F (n + 1) p v = cxML F n (p.curryLeft (Cx.re (v 0))) (Fin.tail v) +
      Complex.I • cxML F n (p.curryLeft (Cx.im (v 0))) (Fin.tail v) := by
  rw [cxML_succ_eq, ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply]

/-- `‖cxML F n‖ ≤ 2ⁿ`. -/
theorem norm_cxML_le : ∀ n : ℕ, ‖cxML F n‖ ≤ 2 ^ n
  | 0 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxML_zero_eq, ContinuousMultilinearMap.norm_constOfIsEmpty, Cx.norm_ι, pow_zero, one_mul]
    exact (p.le_opNorm 0).trans (by simp)
  | n + 1 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxML_succ_eq, ContinuousLinearMap.uncurryLeft_norm]
    calc ‖cxLin ((cxML F n).comp p.curryLeft)‖ ≤ 2 * ‖(cxML F n).comp p.curryLeft‖ := norm_cxLin_le _
      _ ≤ 2 * (‖cxML F n‖ * ‖p.curryLeft‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (2 ^ n * ‖p‖) := by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        gcongr
        exact norm_cxML_le n
      _ = 2 ^ (n + 1) * ‖p‖ := by ring

/-- `‖q_n‖ ≤ 2ⁿ ‖p_n‖`. -/
theorem norm_cxML_apply_le {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => F) F) :
    ‖cxML F n p‖ ≤ 2 ^ n * ‖p‖ :=
  ((cxML F n).le_opNorm p).trans (mul_le_mul_of_nonneg_right (norm_cxML_le n) (norm_nonneg _))

/-- **Agreement at real points**: `q_n (ι a₁, …, ι aₙ) = ι (p_n (a₁, …, aₙ))`. -/
theorem cxML_ι : ∀ (n : ℕ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => F) F) (a : Fin n → F),
    cxML F n p (fun i => Cx.ι (a i)) = Cx.ι (p a)
  | 0, p, a => by
    rw [cxML_zero_apply, Subsingleton.elim a 0]
  | n + 1, p, a => by
    rw [cxML_succ_apply]
    simp only [Cx.re_ι, Cx.im_ι, map_zero, zero_apply, smul_zero, add_zero]
    have h := cxML_ι n (p.curryLeft (a 0)) (Fin.tail a)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Termwise complexification of a real formal multilinear series. -/
def cxSeries (p : FormalMultilinearSeries ℝ F F) : FormalMultilinearSeries ℂ (Cx F) (Cx F) :=
  fun n => cxML F n (p n)

theorem norm_cxSeries_le (p : FormalMultilinearSeries ℝ F F) (n : ℕ) : ‖cxSeries p n‖ ≤ 2 ^ n * ‖p n‖ :=
  norm_cxML_apply_le (p n)

theorem cxSeries_ι (p : FormalMultilinearSeries ℝ F F) (n : ℕ) (y : F) :
    cxSeries p n (fun _ => Cx.ι y) = Cx.ι (p n (fun _ => y)) :=
  cxML_ι n (p n) (fun _ => y)

end QuantumNLS.ProductTorusComplexMultilinear

#print axioms QuantumNLS.ProductTorusComplexMultilinear.cxLin
#print axioms QuantumNLS.ProductTorusComplexMultilinear.norm_cxLin_le
#print axioms QuantumNLS.ProductTorusComplexMultilinear.cxML
#print axioms QuantumNLS.ProductTorusComplexMultilinear.norm_cxML_le
#print axioms QuantumNLS.ProductTorusComplexMultilinear.norm_cxML_apply_le
#print axioms QuantumNLS.ProductTorusComplexMultilinear.cxML_ι
#print axioms QuantumNLS.ProductTorusComplexMultilinear.norm_cxSeries_le
#print axioms QuantumNLS.ProductTorusComplexMultilinear.cxSeries_ι
