import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-!
# R-4C2E4AC7, stage C1 (Terra r167 item (c), part 1): the complexification of a real inner product space

Source: `chapters/global/product_torus.tex`, theorem, lines 39–41 ("Near each fixed `u`, the maps `T_θ` have holomorphic
extensions in the complexified initial variable to one common neighborhood, bounded there uniformly over the whole
product group").

Mathlib at this pin has no complexification of a real normed space. For a real inner product space `F` this module
builds `Cx F = F × F` (as `WithLp 2 (F × F)`, a type synonym that does not inherit any scalar action) with
`(x + iy)(a, b) = (xa − yb, xb + ya)` and the Hilbert norm `‖(a,b)‖² = ‖a‖² + ‖b‖²`, and proves:
* `Cx.module`: a `ℂ`-module; `Cx.norm_smul_sq`: `‖c • z‖² = ‖c‖²‖z‖²` (real inner-product cross terms cancel), hence a
  complex normed space (`Cx.normedSpace`), complete when `F` is;
* the real embedding `ι a = (a, 0)`: isometric (`norm_ι`), additive, `ι (r • a) = (r : ℂ) • ι a`, and every point is
  `mk a b = ι a + i • ι b` (`mk_eq`), so `ι F` is a totally real subspace with `Cx F = ι F ⊕ i ι F`.
Remaining for item (c) (next stages, see the hand-back): complexification of continuous real multilinear maps with
`‖p̃_n‖ ≤ 2^{n+1} ‖p_n‖`, and the series extension of `T_ψ` with the uniform bound on the `r/4` complex ball.
-/

set_option autoImplicit false

noncomputable section

namespace QuantumNLS.ProductTorusComplexification

/-- The complexification `F × F` of a real inner product space, with the Hilbert norm. -/
def Cx (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] : Type _ := WithLp 2 (F × F)

namespace Cx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

instance : NormedAddCommGroup (Cx F) := inferInstanceAs (NormedAddCommGroup (WithLp 2 (F × F)))

/-- Real part. -/
def re (z : Cx F) : F := (WithLp.ofLp (z : WithLp 2 (F × F))).1

/-- Imaginary part. -/
def im (z : Cx F) : F := (WithLp.ofLp (z : WithLp 2 (F × F))).2

/-- The point `a + i b`. -/
def mk (a b : F) : Cx F := WithLp.toLp 2 (a, b)

@[simp] theorem re_mk (a b : F) : re (mk a b) = a := rfl
@[simp] theorem im_mk (a b : F) : im (mk a b) = b := rfl
@[simp] theorem re_add (z w : Cx F) : re (z + w) = re z + re w := rfl
@[simp] theorem im_add (z w : Cx F) : im (z + w) = im z + im w := rfl
@[simp] theorem re_zero : re (0 : Cx F) = 0 := rfl
@[simp] theorem im_zero : im (0 : Cx F) = 0 := rfl
@[simp] theorem re_neg (z : Cx F) : re (-z) = -re z := rfl
@[simp] theorem im_neg (z : Cx F) : im (-z) = -im z := rfl
@[simp] theorem re_sub (z w : Cx F) : re (z - w) = re z - re w := rfl
@[simp] theorem im_sub (z w : Cx F) : im (z - w) = im z - im w := rfl

theorem ext {z w : Cx F} (h1 : re z = re w) (h2 : im z = im w) : z = w :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

theorem norm_sq (z : Cx F) : ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (z : WithLp 2 (F × F))

instance : SMul ℂ (Cx F) := ⟨fun c z => mk (c.re • re z - c.im • im z) (c.re • im z + c.im • re z)⟩

@[simp] theorem re_smul (c : ℂ) (z : Cx F) : re (c • z) = c.re • re z - c.im • im z := rfl
@[simp] theorem im_smul (c : ℂ) (z : Cx F) : im (c • z) = c.re • im z + c.im • re z := rfl

instance module : Module ℂ (Cx F) where
  one_smul z := ext (by simp) (by simp)
  mul_smul c d z := ext (by simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im]; module)
    (by simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im]; module)
  smul_zero c := ext (by simp) (by simp)
  smul_add c z w := ext (by simp only [re_smul, re_add, im_add]; module)
    (by simp only [im_smul, re_add, im_add]; module)
  add_smul c d z := ext (by simp only [re_smul, re_add, Complex.add_re, Complex.add_im]; module)
    (by simp only [im_smul, im_add, Complex.add_re, Complex.add_im]; module)
  zero_smul z := ext (by simp) (by simp)

/-- `‖c • z‖² = ‖c‖² ‖z‖²`. -/
theorem norm_smul_sq (c : ℂ) (z : Cx F) : ‖c • z‖ ^ 2 = ‖c‖ ^ 2 * ‖z‖ ^ 2 := by
  have hc : inner ℝ (im z) (re z) = inner ℝ (re z) (im z) := real_inner_comm _ _
  rw [norm_sq, norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right, hc]
  ring

theorem norm_smul_eq (c : ℂ) (z : Cx F) : ‖c • z‖ = ‖c‖ * ‖z‖ :=
  (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (by rw [mul_pow]; exact norm_smul_sq c z)

instance normedSpace : NormedSpace ℂ (Cx F) where
  norm_smul_le c z := (norm_smul_eq c z).le

instance [CompleteSpace F] : CompleteSpace (Cx F) := inferInstanceAs (CompleteSpace (WithLp 2 (F × F)))

/-- The real embedding `a ↦ a + i 0`. -/
def ι (a : F) : Cx F := mk a 0

@[simp] theorem re_ι (a : F) : re (ι a) = a := rfl
@[simp] theorem im_ι (a : F) : im (ι a) = 0 := rfl

theorem norm_ι (a : F) : ‖ι a‖ = ‖a‖ := by
  have h := norm_sq (ι a)
  rw [re_ι, im_ι, norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem ι_add (a b : F) : ι (a + b) = ι a + ι b := ext (by simp) (by simp)

theorem ι_smul (r : ℝ) (a : F) : ι (r • a) = (r : ℂ) • ι a :=
  ext (by rw [re_ι, re_smul, Complex.ofReal_re, Complex.ofReal_im, re_ι, im_ι, zero_smul, sub_zero])
    (by rw [im_ι, im_smul, Complex.ofReal_re, Complex.ofReal_im, im_ι, re_ι, smul_zero, zero_smul, add_zero])

theorem mk_eq (a b : F) : mk a b = ι a + Complex.I • ι b := ext (by simp) (by simp)

end Cx

end QuantumNLS.ProductTorusComplexification

#print axioms QuantumNLS.ProductTorusComplexification.Cx.module
#print axioms QuantumNLS.ProductTorusComplexification.Cx.norm_smul_eq
#print axioms QuantumNLS.ProductTorusComplexification.Cx.normedSpace
#print axioms QuantumNLS.ProductTorusComplexification.Cx.norm_ι
#print axioms QuantumNLS.ProductTorusComplexification.Cx.mk_eq
