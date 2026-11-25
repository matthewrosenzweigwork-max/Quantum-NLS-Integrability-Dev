import QuantumNLS.RootSymbolConvergence
import QuantumNLS.RootOverlapLimit
import QuantumNLS.TensorPlacements
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# R-C4F43CA8 `thm:root-involution`, part (1): the scalar product symbol is `C¹` on a neighbourhood of the sphere

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` (theorem, first assertion: "They are
continuously Fréchet differentiable on an open neighbourhood of the sphere on which their respective series converge").
Proof route of the source: `‖d(⟨u^{⊗r}, K u^{⊗r}⟩)‖ ≤ 2r‖K‖R^{2r−1}` on `‖u‖ ≤ R`, geometric majorants, termwise
differentiation.

Realized inputs (read-only, frozen): `RootSymbolConvergence` (term bound, `symbolTerm`, `productSymbol`),
`RootPlacementBound.norm_physicalKernel_le` (`‖K_{r,z}‖ ≤ 2 (Im z)^{−r}`, the accepted `lem_root_placement`),
`NormalizedTransfer.orderedKernel = physicalKernel`, `TensorPlacements.extendSymKernel` (norm `≤ ‖A‖`),
`RootOverlapLimit.dP`, `dP_apply`, `hasFDerivAt_htpow`, `htpowML`, `extend_htpow`.

Proved here (standard axioms only, no unproved placeholders):
* `norm_dP_le`: `‖dP_{j+1}(u) h‖ ≤ (j+1) ‖u‖^j ‖h‖`.
* `symFun`, `contDiff_symFun`, `fderiv_symFun_apply`, `norm_fderiv_symFun_le`: the homogeneous symbol
  `v ↦ ⟪v^{⊗n}, A v^{⊗n}⟫` is `C¹` with the derivative formula and the norm bound.
* `contDiffOn_tsum_symFun`: a series `Σ_j w_j symFun_{j+1}(A_j)` with summable bounds on the values and first
  derivatives on `ball 0 R` is `ContDiffOn ℝ 1` there (termwise differentiation via
  `hasFDerivAt_tsum_of_isPreconnected`, continuity of the derivative via `continuousOn_tsum`).
* `productSymbol_contDiffOn`: for `0 ≤ κ < Im z` and `κ R² < Im z`, the scalar product symbol
  `u ↦ productSymbol L κ u z` is `ContDiffOn ℝ 1` on `ball 0 R` (a neighbourhood of the unit sphere when `R > 1`).

Parts (2) (zero reduced Poisson bracket) and (3) (`G_z`) are NOT in this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Set Filter Topology Metric

namespace QuantumNLS.RootSymbolFrechet

open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.RootOverlapLimit
  QuantumNLS.RootOverlapCommutator QuantumNLS.NormalizedTransfer QuantumNLS.RootPlacementBound
  QuantumNLS.RootSymbolConvergence QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_ptC' {n : ℕ} (f : Fin n → H) :
    ‖(ptC f : HilbertTensorPower ℂ H n)‖ = ∏ i, ‖f i‖ := by
  simp [ptC, UniformSpace.Completion.norm_coe, norm_ptprod]

/-- **Derivative of the power map.** `‖dP_{j+1}(u) h‖ ≤ (j+1) ‖u‖^j ‖h‖`. -/
theorem norm_dP_le (j : ℕ) (u h : H) : ‖dP (j + 1) u h‖ ≤ ((j : ℝ) + 1) * ‖u‖ ^ j * ‖h‖ := by
  rw [dP_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  have hterm : ∀ i : Fin (j + 1),
      ‖(ptC (Function.update (fun _ : Fin (j + 1) => u) i h) : HilbertTensorPower ℂ H (j + 1))‖ =
        ‖u‖ ^ j * ‖h‖ := by
    intro i
    rw [norm_ptC']
    have hfun : (fun k => ‖Function.update (fun _ : Fin (j + 1) => u) i h k‖) =
        Function.update (fun _ : Fin (j + 1) => ‖u‖) i ‖h‖ := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp [Finset.prod_const, Finset.card_univ_diff]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The homogeneous symbol `v ↦ ⟪v^{⊗n}, A v^{⊗n}⟫` on the completed tensor power. -/
def symFun (n : ℕ) (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (v : H) : ℂ :=
  ⟪(htpow n v : HilbertTensorPower ℂ H n), A (htpow n v)⟫_ℂ

theorem contDiff_htpow' (n : ℕ) :
    ContDiff ℝ 1 (fun v : H => (htpow n v : HilbertTensorPower ℂ H n)) := by
  have hd : ContDiff ℝ 1 (fun v : H => (fun _ : Fin n => v)) := contDiff_pi.2 (fun _ => contDiff_id)
  have h2 : ContDiff ℝ 1 (fun v : H => htpowML (H := H) n (fun _ : Fin n => v)) :=
    (htpowML (H := H) n).contDiff.comp hd
  have h3 : (fun v : H => htpowML (H := H) n (fun _ : Fin n => v)) =
      (fun v : H => (htpow n v : HilbertTensorPower ℂ H n)) := by
    funext v
    rw [htpowML_apply]
    rfl
  rw [h3] at h2
  exact h2

theorem contDiff_symFun' (n : ℕ) (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    ContDiff ℝ 1 (symFun n A) := by
  have hA : ContDiff ℝ 1 (fun v : H => A (htpow n v : HilbertTensorPower ℂ H n)) :=
    (A.restrictScalars ℝ).contDiff.comp (contDiff_htpow' n)
  exact ContDiff.inner ℂ (contDiff_htpow' n) hA

theorem fderiv_symFun_apply (n : ℕ) (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
    (u h : H) :
    fderiv ℝ (symFun n A) u h =
      ⟪(htpow n u : HilbertTensorPower ℂ H n), A (dP n u h)⟫_ℂ +
        ⟪dP n u h, A (htpow n u)⟫_ℂ := by
  have hf : HasFDerivAt (fun v : H => (htpow n v : HilbertTensorPower ℂ H n)) (dP n u) u :=
    hasFDerivAt_htpow n u
  have hg : HasFDerivAt (fun v : H => A (htpow n v : HilbertTensorPower ℂ H n))
      ((A.restrictScalars ℝ).comp (dP n u)) u :=
    (A.restrictScalars ℝ).hasFDerivAt.comp u hf
  have hL := HasFDerivAt.inner ℂ hf hg
  have hsymFun : symFun n A = fun t => ⟪(htpow n t : HilbertTensorPower ℂ H n), A (htpow n t)⟫_ℂ := rfl
  rw [hsymFun, hL.fderiv]
  simp [fderivInnerCLM_apply]

/-- **Derivative bound.** For `j ≥ 0`: `‖d symFun_{j+1}(A)(u)‖ ≤ 2 (j+1) ‖A‖ ‖u‖^{j+1} ‖u‖^j`. -/
theorem norm_fderiv_symFun_le (j : ℕ) (A : HilbertTensorPower ℂ H (j + 1) →L[ℂ] HilbertTensorPower ℂ H (j + 1))
    (u : H) :
    ‖fderiv ℝ (symFun (j + 1) A) u‖ ≤
      2 * ((j : ℝ) + 1) * ‖A‖ * ‖u‖ ^ (j + 1) * ‖u‖ ^ j := by
  have hM : 0 ≤ 2 * ((j : ℝ) + 1) * ‖A‖ * ‖u‖ ^ (j + 1) * ‖u‖ ^ j := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun h => ?_)
  rw [fderiv_symFun_apply]
  set x : HilbertTensorPower ℂ H (j + 1) := (htpow (j + 1) u : HilbertTensorPower ℂ H (j + 1)) with hx
  have hxn : ‖x‖ = ‖u‖ ^ (j + 1) := norm_htpow (j + 1) u
  have hdn := norm_dP_le j u h
  have ha : ‖A (dP (j + 1) u h)‖ ≤ ‖A‖ * ‖dP (j + 1) u h‖ := ContinuousLinearMap.le_opNorm _ _
  have hb : ‖A x‖ ≤ ‖A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have h1 : ‖⟪x, A (dP (j + 1) u h)⟫_ℂ‖ ≤ ‖x‖ * (‖A‖ * ‖dP (j + 1) u h‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
  have h2 : ‖⟪dP (j + 1) u h, A x⟫_ℂ‖ ≤ ‖dP (j + 1) u h‖ * (‖A‖ * ‖x‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  calc ‖⟪x, A (dP (j + 1) u h)⟫_ℂ + ⟪dP (j + 1) u h, A x⟫_ℂ‖
      ≤ ‖⟪x, A (dP (j + 1) u h)⟫_ℂ‖ + ‖⟪dP (j + 1) u h, A x⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖dP (j + 1) u h‖) + ‖dP (j + 1) u h‖ * (‖A‖ * ‖x‖) := add_le_add h1 h2
    _ ≤ ‖u‖ ^ (j + 1) * (‖A‖ * (((j : ℝ) + 1) * ‖u‖ ^ j * ‖h‖)) +
          ((((j : ℝ) + 1) * ‖u‖ ^ j * ‖h‖)) * (‖A‖ * ‖u‖ ^ (j + 1)) := by
        rw [hxn]
        gcongr
    _ = 2 * ((j : ℝ) + 1) * ‖A‖ * ‖u‖ ^ (j + 1) * ‖u‖ ^ j * ‖h‖ := by ring

end Generic


section Series

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem summable_bound (q R : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun j : ℕ => (2 + 4 * ((j : ℝ) + 1) / R) * q ^ (j + 1)) := by
  have hq' : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq
  have hS0 : Summable (fun j : ℕ => q ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq)
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (1 : ℕ) * q ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hq'
  have hS1 : Summable (fun j : ℕ => ((j : ℝ) + 1) * q ^ (j + 1)) := by
    have h : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (1 : ℕ) * q ^ (j + 1)) :=
      (summable_nat_add_iff 1).mpr h1
    refine h.congr (fun j => ?_)
    push_cast
    ring
  have h2 : Summable (fun j : ℕ => 2 * q ^ (j + 1) + (4 / R) * (((j : ℝ) + 1) * q ^ (j + 1))) :=
    (hS0.mul_left 2).add (hS1.mul_left (4 / R))
  refine h2.congr (fun j => ?_)
  ring

/-- **Termwise `C¹` of a symmetric symbol series on a ball.** Coefficients `w_j`, kernels `A_j`, and
`‖w_j‖ ‖A_j‖ R^{2(j+1)} ≤ 2 q^{j+1}` with `0 ≤ q < 1`. -/
theorem contDiffOn_tsum_symFun (w : ℕ → ℂ)
    (A : ∀ j : ℕ, HilbertTensorPower ℂ H (j + 1) →L[ℂ] HilbertTensorPower ℂ H (j + 1))
    {R q : ℝ} (hR : 0 < R) (hq0 : 0 ≤ q) (hq : q < 1)
    (hb : ∀ j : ℕ, ‖w j‖ * ‖A j‖ * R ^ (j + 1) * R ^ (j + 1) ≤ 2 * q ^ (j + 1)) :
    ContDiffOn ℝ 1 (fun v : H => ∑' j : ℕ, w j * symFun (j + 1) (A j) v) (ball (0 : H) R) := by
  set u : ℕ → ℝ := fun j => (2 + 4 * ((j : ℝ) + 1) / R) * q ^ (j + 1) with hu_def
  have hsum : Summable u := summable_bound q R hq0 hq
  have hval : ∀ j : ℕ, ∀ v ∈ ball (0 : H) R, ‖w j * symFun (j + 1) (A j) v‖ ≤ u j := by
    intro j v hv
    have hvR : ‖v‖ ≤ R := (mem_ball_zero_iff.mp hv).le
    have hxR : ‖(htpow (j + 1) v : HilbertTensorPower ℂ H (j + 1))‖ ≤ R ^ (j + 1) := by
      rw [norm_htpow]; exact pow_le_pow_left₀ (norm_nonneg _) hvR _
    have hsym : ‖symFun (j + 1) (A j) v‖ ≤ ‖A j‖ * R ^ (j + 1) * R ^ (j + 1) := by
      unfold symFun
      refine (norm_inner_le_norm _ _).trans ?_
      have hAx : ‖A j (htpow (j + 1) v : HilbertTensorPower ℂ H (j + 1))‖ ≤ ‖A j‖ * R ^ (j + 1) :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hxR (norm_nonneg _))
      exact (mul_le_mul hxR hAx (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring))
    have hq1 : 0 ≤ q ^ (j + 1) := pow_nonneg hq0 _
    have hu_ge : 2 * q ^ (j + 1) ≤ u j := by
      simp only [hu_def]
      have h4 : 0 ≤ 4 * ((j : ℝ) + 1) / R * q ^ (j + 1) := by positivity
      nlinarith [h4]
    calc ‖w j * symFun (j + 1) (A j) v‖ = ‖w j‖ * ‖symFun (j + 1) (A j) v‖ := norm_mul _ _
      _ ≤ ‖w j‖ * (‖A j‖ * R ^ (j + 1) * R ^ (j + 1)) :=
          mul_le_mul_of_nonneg_left hsym (norm_nonneg _)
      _ = ‖w j‖ * ‖A j‖ * R ^ (j + 1) * R ^ (j + 1) := by ring
      _ ≤ 2 * q ^ (j + 1) := hb j
      _ ≤ u j := hu_ge
  have hder : ∀ j : ℕ, ∀ v ∈ ball (0 : H) R, ‖w j • fderiv ℝ (symFun (j + 1) (A j)) v‖ ≤ u j := by
    intro j v hv
    have hvR : ‖v‖ ≤ R := (mem_ball_zero_iff.mp hv).le
    rw [norm_smul]
    have hd := norm_fderiv_symFun_le j (A j) v
    have hpow : ‖v‖ ^ (j + 1) * ‖v‖ ^ j ≤ R ^ (j + 1) * R ^ j :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hvR _) (pow_le_pow_left₀ (norm_nonneg _) hvR _)
        (by positivity) (by positivity)
    have hkey' : ‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j) * R ≤ 2 * q ^ (j + 1) := by
      calc ‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j) * R
          = ‖w j‖ * ‖A j‖ * R ^ (j + 1) * R ^ (j + 1) := by ring
        _ ≤ 2 * q ^ (j + 1) := hb j
    have hX : ‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j) ≤ 2 * q ^ (j + 1) / R := by
      rw [le_div_iff₀ hR]; exact hkey'
    have hfin : ‖w j‖ * (2 * ((j : ℝ) + 1) * ‖A j‖ * ‖v‖ ^ (j + 1) * ‖v‖ ^ j) ≤
        2 * ((j : ℝ) + 1) * (‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j)) := by
      calc ‖w j‖ * (2 * ((j : ℝ) + 1) * ‖A j‖ * ‖v‖ ^ (j + 1) * ‖v‖ ^ j)
          = 2 * ((j : ℝ) + 1) * ‖w j‖ * ‖A j‖ * (‖v‖ ^ (j + 1) * ‖v‖ ^ j) := by ring
        _ ≤ 2 * ((j : ℝ) + 1) * ‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j) := by
            apply mul_le_mul_of_nonneg_left hpow
            positivity
        _ = 2 * ((j : ℝ) + 1) * (‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j)) := by ring
    have hq1 : 0 ≤ q ^ (j + 1) := pow_nonneg hq0 _
    have e : u j = 2 * q ^ (j + 1) + 4 * ((j : ℝ) + 1) / R * q ^ (j + 1) := by
      simp only [hu_def]; ring
    have e2 : 2 * ((j : ℝ) + 1) * (2 * q ^ (j + 1) / R) = 4 * ((j : ℝ) + 1) / R * q ^ (j + 1) := by
      ring
    calc ‖w j‖ * ‖fderiv ℝ (symFun (j + 1) (A j)) v‖
        ≤ ‖w j‖ * (2 * ((j : ℝ) + 1) * ‖A j‖ * ‖v‖ ^ (j + 1) * ‖v‖ ^ j) :=
          mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ 2 * ((j : ℝ) + 1) * (‖w j‖ * ‖A j‖ * (R ^ (j + 1) * R ^ j)) := hfin
      _ ≤ 2 * ((j : ℝ) + 1) * (2 * q ^ (j + 1) / R) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 4 * ((j : ℝ) + 1) / R * q ^ (j + 1) := e2
      _ ≤ u j := by rw [e]; linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq1]
  have hfd : ∀ j : ℕ, ∀ v : H,
      HasFDerivAt (fun y => w j * symFun (j + 1) (A j) y) (w j • fderiv ℝ (symFun (j + 1) (A j)) v) v :=
    fun j v => ((contDiff_symFun' (j + 1) (A j)).differentiable one_ne_zero v).hasFDerivAt.const_mul (w j)
  have hf0 : Summable (fun j : ℕ => w j * symFun (j + 1) (A j) 0) :=
    Summable.of_norm_bounded (g := u) hsum (fun j => hval j 0 (mem_ball_self hR))
  have hdiff : ∀ v ∈ ball (0 : H) R,
      HasFDerivAt (fun y => ∑' j : ℕ, w j * symFun (j + 1) (A j) y)
        (∑' j : ℕ, w j • fderiv ℝ (symFun (j + 1) (A j)) v) v := fun v hv =>
    hasFDerivAt_tsum_of_isPreconnected hsum isOpen_ball (convex_ball _ _).isPreconnected
      (fun j y _ => hfd j y) (fun j y hy => hder j y hy) (mem_ball_self hR) hf0 hv
  have hfderiv_eq : ∀ v ∈ ball (0 : H) R,
      fderiv ℝ (fun y => ∑' j : ℕ, w j * symFun (j + 1) (A j) y) v =
        ∑' j : ℕ, w j • fderiv ℝ (symFun (j + 1) (A j)) v :=
    fun v hv => (hdiff v hv).fderiv
  have hcont : ContinuousOn (fun v : H => ∑' j : ℕ, w j • fderiv ℝ (symFun (j + 1) (A j)) v)
      (ball (0 : H) R) := by
    refine continuousOn_tsum (fun j => ?_) hsum (fun j v hv => hder j v hv)
    exact ((((contDiff_symFun' (j + 1) (A j)).continuous_fderiv one_ne_zero).continuousOn)).const_smul (w j)
  have hdiffOn : DifferentiableOn ℝ (fun y => ∑' j : ℕ, w j * symFun (j + 1) (A j) y)
      (ball (0 : H) R) := fun v hv => (hdiff v hv).differentiableAt.differentiableWithinAt
  have hfderivCont : ContinuousOn (fderiv ℝ (fun y => ∑' j : ℕ, w j * symFun (j + 1) (A j) y))
      (ball (0 : H) R) := hcont.congr (fun v hv => hfderiv_eq v hv)
  have hC := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) isOpen_ball).mpr
    ⟨hdiffOn, fun h => absurd h (by simp), contDiffOn_zero.mpr hfderivCont⟩
  simpa using hC

/-- The complex coefficient `κ^{j+1}` of the `(j+1)`-th term. -/
def physW (κ : ℝ) (j : ℕ) : ℂ := ((κ ^ (j + 1) : ℝ) : ℂ)

end Series

section Physical

variable (L : ℝ) [Fact (0 < L)]

/-- The symmetric extension of the kernel `K_{j+1,z}` on the completed tensor power. -/
def physA (z : ℂ) (j : ℕ) :
    HilbertTensorPower ℂ (L2T L) (j + 1) →L[ℂ] HilbertTensorPower ℂ (L2T L) (j + 1) :=
  extendSymKernel (orderedKernel L (j + 1) z)

theorem symbolTerm_eq_symFun (κ : ℝ) (z : ℂ) (j : ℕ) (u : L2T L) :
    symbolTerm L κ u z (j + 1) = physW κ j * symFun (j + 1) (physA L z j) u := by
  have hk : kernelProductSymbol (orderedKernel L (j + 1) z) u =
      symFun (j + 1) (physA L z j) u := by
    unfold symFun kernelProductSymbol physA
    rw [extend_htpow]
    rfl
  unfold symbolTerm physW
  rw [hk]

/-- **Part (1) for the scalar product symbol.** For `0 ≤ κ < Im z` and `κ R² < Im z`, the symbol
`u ↦ productSymbol L κ u z` is `C¹` on the open ball `‖u‖ < R` (a neighbourhood of the unit sphere when `R > 1`). -/
theorem productSymbol_contDiffOn (κ : ℝ) (hκ : 0 ≤ κ) (z : ℂ) (hκz : κ < z.im)
    (R : ℝ) (hR : 0 < R) (hRz : κ * R ^ 2 < z.im) :
    ContDiffOn ℝ 1 (fun u : L2T L => productSymbol L κ u z) (ball (0 : L2T L) R) := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ hκz
  have hq0 : 0 ≤ κ * R ^ 2 / z.im := by positivity
  have hq : κ * R ^ 2 / z.im < 1 := (div_lt_one hη).mpr hRz
  have hb : ∀ j : ℕ, ‖physW κ j‖ * ‖physA L z j‖ * R ^ (j + 1) * R ^ (j + 1) ≤
      2 * (κ * R ^ 2 / z.im) ^ (j + 1) := by
    intro j
    have hK := norm_physicalKernel_le (L := L) (r := j + 1) (by omega) z hη
    have hAn : ‖physA L z j‖ ≤ 2 * (z.im)⁻¹ ^ (j + 1) := (norm_extendSymKernel_le _).trans hK
    have hwn : ‖physW κ j‖ = κ ^ (j + 1) := by
      unfold physW
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ _)]
    rw [hwn]
    calc κ ^ (j + 1) * ‖physA L z j‖ * R ^ (j + 1) * R ^ (j + 1)
        ≤ κ ^ (j + 1) * (2 * (z.im)⁻¹ ^ (j + 1)) * R ^ (j + 1) * R ^ (j + 1) := by gcongr
      _ = 2 * (κ * R ^ 2 / z.im) ^ (j + 1) := by
          rw [div_eq_mul_inv, mul_pow, mul_pow, inv_pow]; ring
  have hfun : (fun u : L2T L => productSymbol L κ u z) =
      fun u : L2T L => (1 + Complex.exp (Complex.I * z * L)) +
        ∑' j : ℕ, physW κ j * symFun (j + 1) (physA L z j) u := by
    funext u
    unfold productSymbol
    rw [show (∑' j : ℕ, symbolTerm L κ u z (j + 1)) =
        ∑' j : ℕ, physW κ j * symFun (j + 1) (physA L z j) u from
        tsum_congr (fun j => symbolTerm_eq_symFun L κ z j u)]
  rw [hfun]
  exact contDiffOn_const.add
    (contDiffOn_tsum_symFun (physW κ) (physA L z) hR hq0 hq hb)

end Physical

end QuantumNLS.RootSymbolFrechet

#print axioms QuantumNLS.RootSymbolFrechet.norm_dP_le
#print axioms QuantumNLS.RootSymbolFrechet.norm_fderiv_symFun_le
#print axioms QuantumNLS.RootSymbolFrechet.contDiffOn_tsum_symFun
#print axioms QuantumNLS.RootSymbolFrechet.productSymbol_contDiffOn
