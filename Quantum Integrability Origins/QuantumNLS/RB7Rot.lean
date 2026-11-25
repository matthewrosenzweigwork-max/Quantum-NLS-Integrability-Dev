import Mathlib
import QuantumNLS.SobolevSpaces

/-!
# R-7B122087 `thm:hierarchy` (`DYNAMICS_LEMMAS.tex:115`), stage S: coordinatewise rotations, the complex coordinate
gradient and the division-free Hessian estimate on a weighted sequence space

Pure functional analysis on the DEF-002-type weighted sequence spaces `WSeq W` (`SobolevSpaces`).  Nothing here uses
REG-015, DEF-024 or any chart.  Printed proof (second paragraph of `thm:hierarchy`):

* "`F_r` is invariant under all coordinatewise rotations", "Define its complex coordinate gradient `w_j` by
  `dF_r(z)[η e_j] = Re(conj(w_j(z)) η)`.  Rotation invariance gives `w_j(z) = ω_{r,j}(z) z_j`, with real `ω_{r,j}` for nonzero
  `z_j`, and `w_j(z) = 0` at zero coordinates.  The active frequencies are constant on each full modulus torus.";
* "the coordinate-erasure set `{z - τ z_j e_j}` ... The `C²` Hessian is bounded on this set.  Integrating it from the point
  with the `j`th coordinate erased gives `|w_j(z)| ≤ C_z (1+j²)^s |z_j|`, `|ω_{r,j}(z)| ≤ C_z (1+j²)^s`."

Normalization used here (DEF-015): for a real-linear functional `ℓ` on `WSeq W`, `grad ℓ j := (ℓ(e_j) + i ℓ(i e_j)) / 2`
so that `ℓ(c e_j) = 2 Re(conj(grad ℓ j) c)`, i.e. `dF(z)[h] = 2 Re ⟨∇F, h⟩` (the DEF-015 gradient `HierarchyFlow.IsSmoothGradient`);
the printed `w_j` is `2 grad` (printed `dF[η e_j] = Re(conj(w_j) η)` in the `Z`-coordinate normalization of `{Z, conj Z} = -2i`).
The frequency `Ω = Re(conj(z_j) grad_j)/|z_j|²` is the rotation rate of the flow `ż = -i ∇F`; it is unchanged by the constant
rescaling `Z = √2 w` of coordinates, so it is the printed `ω_{r,j}` (printed "no extra factor of two").

Contents: `rot` (unimodular multipliers, `ℂ`-linear isometry), `ev` (unit vectors, `‖ev j‖² = W_j`), `grad`, equivariance
`grad_rot`, vanishing at zero coordinates `grad_zero`, tangency `grad_tangent`, `grad_eq_freq_mul`, invariance `freq_rot`,
the Hessian estimate `grad_bound` / `freq_bound`, continuity `freq_continuousAt` at nonzero coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

variable {W : PosWeight}

/-! ## Coordinates -/

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  push_neg at hab
  nlinarith

theorem w_mul_sq_le (z : WSeq W) (j : ℤ) : W.w j * ‖z.val j‖ ^ 2 ≤ ‖z‖ ^ 2 :=
  le_hasSum (hasSum_norm_sq W z) j (fun n _ => mul_nonneg (W.pos n).le (sq_nonneg _))

theorem sqrt_w_mul_norm_le (z : WSeq W) (j : ℤ) : Real.sqrt (W.w j) * ‖z.val j‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq' (norm_nonneg _) ?_
  rw [mul_pow, Real.sq_sqrt (W.pos j).le]
  exact w_mul_sq_le z j

/-- The coordinate functional `z ↦ z_j` is continuous. -/
def valCLM (W : PosWeight) (j : ℤ) : WSeq W →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun z => z.val j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } (Real.sqrt (W.w j))⁻¹ (fun z => by
    have h := sqrt_w_mul_norm_le z j
    have hp : 0 < Real.sqrt (W.w j) := Real.sqrt_pos.2 (W.pos j)
    show ‖z.val j‖ ≤ (Real.sqrt (W.w j))⁻¹ * ‖z‖
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith)

theorem continuous_val (j : ℤ) : Continuous fun z : WSeq W => z.val j := (valCLM W j).continuous

/-! ## Rotations -/

/-- Coordinatewise multiplication by unimodular numbers. -/
def rot (u : ℤ → Circle) (z : WSeq W) : WSeq W :=
  WSeq.mk W (fun n => (u n : ℂ) * z.val n) (z.summable.congr fun n => by simp [norm_mul])

@[simp] theorem rot_val (u : ℤ → Circle) (z : WSeq W) (n : ℤ) : (rot u z).val n = (u n : ℂ) * z.val n := rfl

theorem norm_rot (u : ℤ → Circle) (z : WSeq W) : ‖rot u z‖ = ‖z‖ := by
  have h : ‖rot u z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    congr 1
    funext n
    simp
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The rotation as a `ℂ`-linear isometry. -/
def rotL (u : ℤ → Circle) : WSeq W →ₗᵢ[ℂ] WSeq W where
  toFun := rot u
  map_add' x y := WSeq.ext (funext fun n => by simp [mul_add])
  map_smul' c x := WSeq.ext (funext fun n => by simp [mul_left_comm])
  norm_map' z := norm_rot u z

/-- The rotation as a real continuous linear map. -/
def rotCLM (u : ℤ → Circle) : WSeq W →L[ℝ] WSeq W :=
  (rotL u).toContinuousLinearMap.restrictScalars ℝ

@[simp] theorem rotCLM_apply (u : ℤ → Circle) (z : WSeq W) : rotCLM u z = rot u z := rfl

theorem rot_rot (u v : ℤ → Circle) (z : WSeq W) : rot u (rot v z) = rot (u * v) z :=
  WSeq.ext (funext fun n => by simp [mul_assoc])

theorem rot_one (z : WSeq W) : rot (1 : ℤ → Circle) z = z := WSeq.ext (funext fun n => by simp)

theorem rot_comm (u v : ℤ → Circle) (z : WSeq W) : rot u (rot v z) = rot v (rot u z) := by
  rw [rot_rot, rot_rot, mul_comm]

theorem continuous_rot (u : ℤ → Circle) : Continuous (rot u : WSeq W → WSeq W) := (rotL u).continuous

/-! ## Unit vectors -/

/-- The unit vector `e_j`. -/
def ev (W : PosWeight) (j : ℤ) : WSeq W :=
  WSeq.mk W (Pi.single j (1 : ℂ)) (summable_of_ne_finset_zero (s := {j}) fun n hn => by
    have : n ≠ j := by simpa using hn
    simp [Pi.single_apply, this])

theorem ev_val (j n : ℤ) : (ev W j).val n = if n = j then 1 else 0 := by
  simp [ev, Pi.single_apply]

theorem smul_ev_val (c : ℂ) (j n : ℤ) : (c • ev W j).val n = if n = j then c else 0 := by
  simp only [WSeq.val_smul, Pi.smul_apply, smul_eq_mul, ev_val]
  split_ifs <;> simp

theorem norm_ev_sq (j : ℤ) : ‖ev W j‖ ^ 2 = W.w j := by
  rw [norm_sq_eq_tsum, tsum_eq_single j]
  · simp [ev_val]
  · intro n hn
    simp [ev_val, hn]

theorem norm_I_smul (x : WSeq W) : ‖(Complex.I • x)‖ = ‖x‖ := by
  rw [norm_smul]; simp

theorem circle_conj_mul (a : Circle) : conj (a : ℂ) * (a : ℂ) = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

theorem rot_smul_ev (u : ℤ → Circle) (c : ℂ) (j : ℤ) : rot u (c • ev W j) = ((u j : ℂ) * c) • ev W j := by
  refine WSeq.ext (funext fun n => ?_)
  simp only [rot_val, smul_ev_val]
  split_ifs with h
  · subst h; rfl
  · simp

theorem smul_decomp (c : ℂ) (x : WSeq W) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem map_smul_ev (ℓ : WSeq W →L[ℝ] ℝ) (j : ℤ) (c : ℂ) :
    ℓ (c • ev W j) = c.re * ℓ (ev W j) + c.im * ℓ (Complex.I • ev W j) := by
  rw [smul_decomp c (ev W j), map_add, map_smul, map_smul]
  simp

/-! ## The coordinate gradient -/

/-- DEF-015 coordinate gradient of a real-linear functional: `ℓ(c e_j) = 2 Re(conj(grad ℓ j) c)`. -/
def grad (ℓ : WSeq W →L[ℝ] ℝ) (j : ℤ) : ℂ :=
  ⟨ℓ (ev W j) / 2, ℓ (Complex.I • ev W j) / 2⟩

theorem map_smul_ev_eq (ℓ : WSeq W →L[ℝ] ℝ) (j : ℤ) (c : ℂ) :
    ℓ (c • ev W j) = 2 * (conj (grad ℓ j) * c).re := by
  rw [map_smul_ev]
  simp only [grad, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem grad_unique (ℓ : WSeq W →L[ℝ] ℝ) (j : ℤ) (g : ℂ)
    (h : ∀ c : ℂ, ℓ (c • ev W j) = 2 * (conj g * c).re) : grad ℓ j = g := by
  have h1 := h 1
  have h2 := h Complex.I
  rw [one_smul] at h1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im] at h1 h2
  apply Complex.ext
  · simp only [grad]; linarith
  · simp only [grad]; linarith

theorem grad_sub (ℓ₁ ℓ₂ : WSeq W →L[ℝ] ℝ) (j : ℤ) : grad (ℓ₁ - ℓ₂) j = grad ℓ₁ j - grad ℓ₂ j := by
  apply Complex.ext <;> simp [grad] <;> ring

theorem norm_grad_le (ℓ : WSeq W →L[ℝ] ℝ) (j : ℤ) : ‖grad ℓ j‖ ≤ ‖ℓ‖ * ‖ev W j‖ := by
  have h1 : |ℓ (ev W j)| ≤ ‖ℓ‖ * ‖ev W j‖ := by
    have := ℓ.le_opNorm (ev W j); simpa [Real.norm_eq_abs] using this
  have h2 : |ℓ (Complex.I • ev W j)| ≤ ‖ℓ‖ * ‖ev W j‖ := by
    have := ℓ.le_opNorm (Complex.I • ev W j)
    rw [norm_I_smul] at this
    simpa [Real.norm_eq_abs] using this
  calc ‖grad ℓ j‖ ≤ |(grad ℓ j).re| + |(grad ℓ j).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |ℓ (ev W j)| / 2 + |ℓ (Complex.I • ev W j)| / 2 := by
        simp only [grad, abs_div]; norm_num
    _ ≤ ‖ℓ‖ * ‖ev W j‖ := by linarith

/-! ## Rotation-invariant `C²` functionals -/

section Inv

variable {F : WSeq W → ℝ}

theorem fderiv_rot (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (u : ℤ → Circle)
    (z v : WSeq W) : fderiv ℝ F (rot u z) (rot u v) = fderiv ℝ F z v := by
  have h1 : HasFDerivAt (fun x => F (rot u x)) ((fderiv ℝ F (rot u z)).comp (rotCLM u)) z :=
    (hd (rot u z)).hasFDerivAt.comp z (rotCLM u).hasFDerivAt
  have h2 : (fun x => F (rot u x)) = F := funext (hinv u)
  rw [h2] at h1
  have := congrArg (fun T => T v) h1.fderiv
  simpa using this.symm

theorem grad_rot (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (u : ℤ → Circle)
    (z : WSeq W) (j : ℤ) :
    grad (fderiv ℝ F (rot u z)) j = (u j : ℂ) * grad (fderiv ℝ F z) j := by
  apply grad_unique
  intro c
  have hc : c • ev W j = rot u ((conj (u j : ℂ) * c) • ev W j) := by
    rw [rot_smul_ev, ← mul_assoc, mul_comm (u j : ℂ), circle_conj_mul, one_mul]
  rw [hc, fderiv_rot hd hinv u z, map_smul_ev_eq]
  have e : conj (grad (fderiv ℝ F z) j) * (conj (u j : ℂ) * c) =
      conj ((u j : ℂ) * grad (fderiv ℝ F z) j) * c := by rw [map_mul]; ring
  rw [e]

theorem grad_zero (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) (j : ℤ)
    (hz : z.val j = 0) : grad (fderiv ℝ F z) j = 0 := by
  have h1 := grad_rot hd hinv (Pi.mulSingle j (-1 : Circle)) z j
  have h2 : rot (Pi.mulSingle j (-1 : Circle)) z = z := by
    refine WSeq.ext (funext fun n => ?_)
    by_cases hn : n = j
    · subst hn; simp [hz]
    · simp [Pi.mulSingle_eq_of_ne hn]
  rw [h2] at h1
  simp only [Pi.mulSingle_eq_same, Circle.coe_neg, Circle.coe_one] at h1
  have h3 : (2 : ℂ) * grad (fderiv ℝ F z) j = 0 := by linear_combination h1
  simpa using h3

/-- Tangency: the radial structure of `F` in the `j`th coordinate: `dF(z)[i z_j e_j] = 0`. -/
theorem dF_tangent (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) (j : ℤ) :
    fderiv ℝ F z ((Complex.I * z.val j) • ev W j) = 0 := by
  let γ : ℝ → WSeq W := fun t => z + ((Complex.exp (t * Complex.I) - 1) * z.val j) • ev W j
  have hγ : ∀ t : ℝ, γ t = rot (Pi.mulSingle j (Circle.exp t)) z := by
    intro t
    refine WSeq.ext (funext fun n => ?_)
    by_cases hn : n = j
    · subst hn
      simp only [γ, WSeq.val_add, Pi.add_apply, smul_ev_val, if_true, rot_val, Pi.mulSingle_eq_same,
        Circle.coe_exp]
      ring
    · simp [γ, ev_val, hn, Pi.mulSingle_eq_of_ne hn]
  have hder : HasDerivAt γ ((Complex.I * z.val j) • ev W j) 0 := by
    have e1 : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I) - 1) Complex.I ((0 : ℝ) : ℂ) := by
      have := (((hasDerivAt_id' ((0 : ℝ) : ℂ)).mul_const Complex.I).cexp).sub_const 1
      convert this using 1
      simp
    have e2 := (e1.comp_ofReal).mul_const (z.val j)
    have e3 := (e2.smul_const (ev W j)).const_add z
    exact e3
  have hF0 : HasDerivAt (fun t => F (γ t)) (fderiv ℝ F (γ 0) ((Complex.I * z.val j) • ev W j)) 0 :=
    (hd (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hder
  have hγ0 : γ 0 = z := by
    have := hγ 0
    simp [γ] at this ⊢
  have hconst : (fun t => F (γ t)) = fun _ => F z := by
    funext t
    rw [hγ t, hinv]
  rw [hconst] at hF0
  have := hF0.unique (hasDerivAt_const (0 : ℝ) (F z))
  rwa [hγ0] at this

theorem grad_tangent (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) (j : ℤ) :
    (conj (z.val j) * grad (fderiv ℝ F z) j).im = 0 := by
  have h := dF_tangent hd hinv z j
  rw [map_smul_ev_eq] at h
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im] at h ⊢
  linarith

/-- The frequency `Ω_j(z) = Re(conj(z_j) ∇_j F(z)) / |z_j|²` (and `0` at a zero coordinate). -/
def freq (F : WSeq W → ℝ) (z : WSeq W) (j : ℤ) : ℝ :=
  if z.val j = 0 then 0 else (conj (z.val j) * grad (fderiv ℝ F z) j).re / ‖z.val j‖ ^ 2

theorem eq_mul_of_tangent (x g : ℂ) (hx : x ≠ 0) (ht : (conj x * g).im = 0) :
    g = (((conj x * g).re / ‖x‖ ^ 2 : ℝ) : ℂ) * x := by
  have hn : 0 < x.re * x.re + x.im * x.im := by
    rw [← Complex.normSq_apply]; exact Complex.normSq_pos.2 hx
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at ht
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    rw [div_mul_eq_mul_div, eq_div_iff hn.ne']
    linear_combination (-x.im) * ht
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
    rw [div_mul_eq_mul_div, eq_div_iff hn.ne']
    linear_combination x.re * ht

theorem grad_eq_freq_mul (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) (j : ℤ) :
    grad (fderiv ℝ F z) j = (freq F z j : ℂ) * z.val j := by
  by_cases hz : z.val j = 0
  · rw [grad_zero hd hinv z j hz]; simp [freq, hz]
  · have ht := grad_tangent hd hinv z j
    simp only [freq, hz, ite_false]
    exact eq_mul_of_tangent _ _ hz ht

theorem freq_rot (hd : Differentiable ℝ F) (hinv : ∀ u z, F (rot u z) = F z) (u : ℤ → Circle)
    (z : WSeq W) (j : ℤ) : freq F (rot u z) j = freq F z j := by
  by_cases hz : z.val j = 0
  · have : (rot u z).val j = 0 := by simp [hz]
    simp [freq, hz, this]
  · have hz' : (rot u z).val j ≠ 0 := by simp [hz]
    simp only [freq, hz, hz', ite_false]
    rw [grad_rot hd hinv u z j, rot_val]
    congr 1
    · have : conj ((u j : ℂ) * z.val j) * ((u j : ℂ) * grad (fderiv ℝ F z) j) =
          conj (z.val j) * grad (fderiv ℝ F z) j := by
        rw [map_mul]
        calc conj (u j : ℂ) * conj (z.val j) * ((u j : ℂ) * grad (fderiv ℝ F z) j)
            = (conj (u j : ℂ) * (u j : ℂ)) * (conj (z.val j) * grad (fderiv ℝ F z) j) := by ring
          _ = _ := by rw [circle_conj_mul, one_mul]
      rw [this]
    · simp

/-! ### The Hessian estimate -/

theorem grad_bound_seg (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) (j : ℤ)
    (M : ℝ) (hM : ∀ y ∈ segment ℝ (z - z.val j • ev W j) z, ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ M) :
    ‖grad (fderiv ℝ F z) j‖ ≤ M * W.w j * ‖z.val j‖ := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hD1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD1d : Differentiable ℝ (fderiv ℝ F) := hD1.differentiable (by norm_num)
  set zj : WSeq W := z - z.val j • ev W j with hzj
  have hzjv : zj.val j = 0 := by simp [hzj, ev_val]
  have h0 := grad_zero hd hinv zj j hzjv
  have hmv : ‖fderiv ℝ F z - fderiv ℝ F zj‖ ≤ M * ‖z - zj‖ :=
    (convex_segment zj z).norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ F)
      (fun x _ => hD1d x) hM (left_mem_segment ℝ zj z) (right_mem_segment ℝ zj z)
  have hzz : z - zj = z.val j • ev W j := by simp [hzj]
  have hnz : ‖z - zj‖ = ‖z.val j‖ * ‖ev W j‖ := by rw [hzz, norm_smul]
  have hg : grad (fderiv ℝ F z) j = grad (fderiv ℝ F z - fderiv ℝ F zj) j := by
    rw [grad_sub, h0, sub_zero]
  have hev : ‖ev W j‖ * ‖ev W j‖ = W.w j := by rw [← sq, norm_ev_sq]
  calc ‖grad (fderiv ℝ F z) j‖ = ‖grad (fderiv ℝ F z - fderiv ℝ F zj) j‖ := by rw [hg]
    _ ≤ ‖fderiv ℝ F z - fderiv ℝ F zj‖ * ‖ev W j‖ := norm_grad_le _ _
    _ ≤ (M * ‖z - zj‖) * ‖ev W j‖ := mul_le_mul_of_nonneg_right hmv (norm_nonneg _)
    _ = M * ‖z.val j‖ * (‖ev W j‖ * ‖ev W j‖) := by rw [hnz]; ring
    _ = M * W.w j * ‖z.val j‖ := by rw [hev]; ring

theorem grad_bound (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ, ‖grad (fderiv ℝ F z) j‖ ≤ C * W.w j * ‖z.val j‖ := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ F)) := hD1.continuous_fderiv one_ne_zero
  -- uniform bound near `z`
  have hN : Continuous fun y => ‖fderiv ℝ (fderiv ℝ F) y‖ :=
    (continuous_norm (E := WSeq W →L[ℝ] WSeq W →L[ℝ] ℝ)).comp hD2
  obtain ⟨δ, hδ, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ y, dist y z < δ → ‖fderiv ℝ (fderiv ℝ F) y‖ < ‖fderiv ℝ (fderiv ℝ F) z‖ + 1 := by
    have := (hN.continuousAt (x := z)).eventually
      (gt_mem_nhds (lt_add_one ‖fderiv ℝ (fderiv ℝ F) z‖))
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 this
    exact ⟨δ, hδ, fun y hy => h hy⟩
  -- the finitely many coordinates where the erasure moves far
  have hfin : {j : ℤ | ¬ (W.w j * ‖z.val j‖ ^ 2 < δ ^ 2)}.Finite := by
    have h1 := (z.summable.tendsto_cofinite_zero.eventually (gt_mem_nhds (pow_pos hδ 2)))
    exact Filter.eventually_cofinite.1 h1
  have hcomp : ∀ j : ℤ, IsCompact (segment ℝ (z - z.val j • ev W j) z) := fun j => by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  choose B hB using fun j : ℤ =>
    (hcomp j).exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ F)) hD2.continuousOn
  set M : ℝ := ‖fderiv ℝ (fderiv ℝ F) z‖ + 1 + ∑ j ∈ hfin.toFinset, |B j| with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑ j ∈ hfin.toFinset, |B j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have := norm_nonneg (fderiv ℝ (fderiv ℝ F) z)
    linarith
  refine ⟨M, hM0, fun j => grad_bound_seg hF hinv z j M (fun y hy => ?_)⟩
  by_cases hj : j ∈ hfin.toFinset
  · have h1 : ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ B j := hB j y hy
    have h2 : B j ≤ |B j| := le_abs_self _
    have h3 : |B j| ≤ ∑ j ∈ hfin.toFinset, |B j| :=
      Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) hj
    have := norm_nonneg (fderiv ℝ (fderiv ℝ F) z)
    linarith
  · have hjn : W.w j * ‖z.val j‖ ^ 2 < δ ^ 2 := by
      by_contra h
      exact hj (by simpa using h)
    have hnorm : ‖z.val j • ev W j‖ < δ := by
      rw [norm_smul]
      refine lt_of_pow_lt_pow_left₀ 2 hδ.le ?_
      rw [mul_pow, norm_ev_sq]
      linarith
    have hball : segment ℝ (z - z.val j • ev W j) z ⊆ Metric.ball z δ := by
      refine (convex_ball z δ).segment_subset ?_ (Metric.mem_ball_self hδ)
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hnorm
    have := hδb y (hball hy)
    have hs : 0 ≤ ∑ j ∈ hfin.toFinset, |B j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith

theorem freq_bound (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z) (z : WSeq W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℤ, |freq F z j| ≤ C * W.w j := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  obtain ⟨C, hC0, hC⟩ := grad_bound hF hinv z
  refine ⟨C, hC0, fun j => ?_⟩
  by_cases hz : z.val j = 0
  · simp only [freq, hz, if_true, abs_zero]
    exact mul_nonneg hC0 (W.pos j).le
  · have h1 := hC j
    rw [grad_eq_freq_mul hd hinv z j, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    have hp : 0 < ‖z.val j‖ := norm_pos_iff.2 hz
    nlinarith

/-! ### Continuity of the frequencies at nonzero coordinates -/

theorem continuous_grad (hF : ContDiff ℝ 2 F) (j : ℤ) :
    Continuous fun y : WSeq W => grad (fderiv ℝ F y) j := by
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have h1 : Continuous fun y : WSeq W => fderiv ℝ F y (ev W j) := hc.clm_apply continuous_const
  have h2 : Continuous fun y : WSeq W => fderiv ℝ F y (Complex.I • ev W j) := hc.clm_apply continuous_const
  have e : (fun y : WSeq W => grad (fderiv ℝ F y) j) =
      fun y => ((fderiv ℝ F y (ev W j) / 2 : ℝ) : ℂ) + ((fderiv ℝ F y (Complex.I • ev W j) / 2 : ℝ) : ℂ) * Complex.I := by
    funext y; apply Complex.ext <;> simp [grad]
  rw [e]
  exact (Complex.continuous_ofReal.comp (h1.div_const 2)).add
    ((Complex.continuous_ofReal.comp (h2.div_const 2)).mul continuous_const)

theorem freq_continuousAt (hF : ContDiff ℝ 2 F) (z : WSeq W) (j : ℤ) (hz : z.val j ≠ 0) :
    ContinuousAt (fun y => freq F y j) z := by
  have hv : ContinuousAt (fun y : WSeq W => y.val j) z := (continuous_val j).continuousAt
  have hev : ∀ᶠ y in 𝓝 z, y.val j ≠ 0 := hv.eventually_ne hz
  have hcont : ContinuousAt (fun y : WSeq W => (conj (y.val j) * grad (fderiv ℝ F y) j).re / ‖y.val j‖ ^ 2) z := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (Complex.continuous_re.continuousAt).comp
        ((Complex.continuous_conj.continuousAt.comp hv).mul (continuous_grad hF j).continuousAt)
    · exact (hv.norm).pow 2
    · positivity
  refine hcont.congr ?_
  filter_upwards [hev] with y hy
  simp [freq, hy]

end Inv

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.grad_bound
#print axioms QuantumNLS.RB7.freq_rot
#print axioms QuantumNLS.RB7.grad_eq_freq_mul
#print axioms QuantumNLS.RB7.freq_continuousAt
#print axioms QuantumNLS.RB7.freq_bound
