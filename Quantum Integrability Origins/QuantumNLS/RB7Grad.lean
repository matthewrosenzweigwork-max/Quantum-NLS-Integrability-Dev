import Mathlib
import QuantumNLS.RB7Seq

/-!
# R-7B122087 `thm:hierarchy`, gradient identification (abstract part)

Printed: "Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with `-i∇I_{r+1}(u(t))`.  The test gradients and
vectors are smooth and the sums converge, so no unbounded Hamiltonian is differentiated at rough data."

* `dF_hasSum` (sequence side): for `F` differentiable at `z` on `WSeq W` and `G_j = grad_j F(z)` with `Σ |G_j|²/W_j < ∞`,
  `dF(z)[w] = 2 Re Σ_j conj(G_j) w_j` for every `w ∈ WSeq W` (finite-support formula + density).
* `dI_eq` (chart side, abstract): `Φ : E → K` with differentiable inverse `Ψ`, strongly symplectic `2 Im⟨DΦ h, DΦ k⟩ = 2 Im⟨h,k⟩`; if
  `dF(Φ u)[DΦ(u)h] = 2 Re⟨i DΦ(u)v, DΦ(u)h⟩` for `F = I ∘ Ψ` then `dI(u)[h] = 2 Re⟨i v, h⟩`, i.e. `v = -i∇I(u)` (DEF-015).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

section Seq

variable {W : PosWeight}

theorem trunc_eq_sum (T : Finset ℤ) (w : WSeq W) : trunc T w = ∑ j ∈ T, w.val j • ev W j := by
  refine WSeq.ext (funext fun n => ?_)
  have : (∑ j ∈ T, w.val j • ev W j).val n = ∑ j ∈ T, (w.val j • ev W j).val n :=
    map_sum (valCLM W n) (fun j => w.val j • ev W j) T
  rw [this]
  simp only [trunc_val, smul_ev_val]
  by_cases hn : n ∈ T
  · simp [hn]
  · simp [hn]

theorem dF_trunc (ℓ : WSeq W →L[ℝ] ℝ) (T : Finset ℤ) (w : WSeq W) :
    ℓ (trunc T w) = 2 * ∑ j ∈ T, (conj (grad ℓ j) * w.val j).re := by
  rw [trunc_eq_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul_ev_eq ℓ j (w.val j)

/-- **`dF(z)[w] = 2 Re Σ_j conj(∇_j F) w_j`** whenever the coordinate gradient lies in the dual weighted `ℓ²`. -/
theorem hasSum_map (ℓ : WSeq W →L[ℝ] ℝ)
    (hG : Summable fun j => ‖grad ℓ j‖ ^ 2 / W.w j) (w : WSeq W) :
    HasSum (fun j => (conj (grad ℓ j) * w.val j).re) (ℓ w / 2) := by
  have hs : Summable fun j => (conj (grad ℓ j) * w.val j).re := by
    refine Summable.of_norm_bounded (g := fun j => (‖grad ℓ j‖ ^ 2 / W.w j + W.w j * ‖w.val j‖ ^ 2) / 2)
      (((hG.add w.summable).div_const 2)) (fun j => ?_)
    have hw := W.pos j
    rw [Real.norm_eq_abs]
    calc |(conj (grad ℓ j) * w.val j).re| ≤ ‖conj (grad ℓ j) * w.val j‖ := Complex.abs_re_le_norm _
      _ = ‖grad ℓ j‖ * ‖w.val j‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ (‖grad ℓ j‖ ^ 2 / W.w j + W.w j * ‖w.val j‖ ^ 2) / 2 := by
          have h1 : ‖grad ℓ j‖ * ‖w.val j‖ = (‖grad ℓ j‖ / Real.sqrt (W.w j)) * (Real.sqrt (W.w j) * ‖w.val j‖) := by
            field_simp [(Real.sqrt_pos.2 hw).ne']
          have h2 : (‖grad ℓ j‖ / Real.sqrt (W.w j)) ^ 2 = ‖grad ℓ j‖ ^ 2 / W.w j := by
            rw [div_pow, Real.sq_sqrt hw.le]
          have h3 : (Real.sqrt (W.w j) * ‖w.val j‖) ^ 2 = W.w j * ‖w.val j‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hw.le]
          rw [h1, ← h2, ← h3]
          nlinarith [sq_nonneg (‖grad ℓ j‖ / Real.sqrt (W.w j) - Real.sqrt (W.w j) * ‖w.val j‖)]
  have h1 : Tendsto (fun T : Finset ℤ => ∑ j ∈ T, (conj (grad ℓ j) * w.val j).re) atTop
      (𝓝 (∑' j, (conj (grad ℓ j) * w.val j).re)) := hs.hasSum
  have h2 : Tendsto (fun T : Finset ℤ => ∑ j ∈ T, (conj (grad ℓ j) * w.val j).re) atTop (𝓝 (ℓ w / 2)) := by
    have h3 : Tendsto (fun T : Finset ℤ => ℓ (trunc T w) / 2) atTop (𝓝 (ℓ w / 2)) :=
      ((ℓ.continuous.tendsto w).comp (tendsto_trunc w)).div_const 2
    refine h3.congr fun T => ?_
    rw [dF_trunc]; ring
  have := tendsto_nhds_unique h1 h2
  have hh := hs.hasSum
  rwa [this] at hh

end Seq

section Chart

variable {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem re_inner_I_smul (x y : E) : (inner ℂ (Complex.I • x) y).re = (inner ℂ x y).im := by
  rw [inner_smul_left]; simp

/-- Abstract Hamiltonian transfer through a strongly symplectic chart. -/
theorem dI_eq (Φ : E → K) (Ψ : K → E) (I : E → ℝ) (u : E)
    (hΦ : DifferentiableAt ℝ Φ u) (hΨ : DifferentiableAt ℝ Ψ (Φ u)) (hΨΦ : ∀ x, Ψ (Φ x) = x)
    (hI : DifferentiableAt ℝ I u)
    (symp : ∀ h k : E, 2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im)
    (v : E) (h : E)
    (hF : fderiv ℝ (fun z => I (Ψ z)) (Φ u) (fderiv ℝ Φ u h) =
      2 * (inner ℂ (Complex.I • fderiv ℝ Φ u v) (fderiv ℝ Φ u h)).re) :
    fderiv ℝ I u h = 2 * (inner ℂ (Complex.I • v) h).re := by
  have hcomp : HasFDerivAt (fun z => I (Ψ z)) ((fderiv ℝ I u).comp (fderiv ℝ Ψ (Φ u))) (Φ u) := by
    have h1 : HasFDerivAt I (fderiv ℝ I u) (Ψ (Φ u)) := by rw [hΨΦ]; exact hI.hasFDerivAt
    exact h1.comp (Φ u) hΨ.hasFDerivAt
  have hid : (fderiv ℝ Ψ (Φ u)).comp (fderiv ℝ Φ u) = ContinuousLinearMap.id ℝ E := by
    have h1 : HasFDerivAt (fun x => Ψ (Φ x)) ((fderiv ℝ Ψ (Φ u)).comp (fderiv ℝ Φ u)) u :=
      hΨ.hasFDerivAt.comp u hΦ.hasFDerivAt
    have h2 : (fun x => Ψ (Φ x)) = id := funext hΨΦ
    rw [h2] at h1
    exact h1.fderiv.symm.trans (fderiv_id) |>.symm ▸ rfl
  rw [hcomp.fderiv] at hF
  have h3 : ((fderiv ℝ I u).comp (fderiv ℝ Ψ (Φ u))) (fderiv ℝ Φ u h) = fderiv ℝ I u h := by
    have := congrArg (fun T => (fderiv ℝ I u) (T h)) hid
    simpa using this
  rw [h3] at hF
  rw [hF, re_inner_I_smul, re_inner_I_smul]
  have := symp v h
  linarith

end Chart

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.hasSum_map
#print axioms QuantumNLS.RB7.dI_eq
