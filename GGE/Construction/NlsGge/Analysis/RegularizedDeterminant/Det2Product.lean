import NlsGge.Analysis.RegularizedDeterminant.Det2
import NlsGge.Analysis.RegularizedDeterminant.TracePairing

/-!
G4: the multiplicative identity

`det₂((I+B)(I+C)) = det₂(I+B) · det₂(I+C) · exp(-tr(BC))`

for all real Hilbert--Schmidt `B, C` (here `(I+B)(I+C) = I + (B + C + BC)` and
`tr(BC) = pairTrace B C = ⟪B*, C⟫_HS`, which is finite because `BC` is a product of two HS
operators; neither `B` nor `C` is assumed trace class), and the consequence that
`det₂(I+B) ≠ 0` whenever `I+B` has a bounded right inverse.

Route: the identity is the finite-dimensional `finiteDet2_product` on a finite-dimensional
subspace containing both ranges when `B, C` have finite rank; both sides are jointly continuous
on `HS × HS` and finite-rank pairs are dense.  Nonvanishing is NOT argued from nonvanishing of
approximants.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The HS product `B C` (composition), as a bounded bilinear map on `HS × HS`. -/
def mulHS : HilbertSchmidt H H →L[ℝ] HilbertSchmidt H H →L[ℝ] HilbertSchmidt H H :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun B C : HilbertSchmidt H H => postcompose (toCLM B) C)
      (fun B B' C => by apply HilbertSchmidt.ext; intro x; simp)
      (fun c B C => by apply HilbertSchmidt.ext; intro x; simp)
      (fun B C C' => by apply HilbertSchmidt.ext; intro x; simp)
      (fun c B C => by apply HilbertSchmidt.ext; intro x; simp))
    1 (fun B C => by
      change ‖postcompose (toCLM B) C‖ ≤ 1 * ‖B‖ * ‖C‖
      rw [one_mul]
      exact (norm_postcompose_le _ _).trans
        (mul_le_mul_of_nonneg_right (opNorm_le B) (norm_nonneg C)))

@[simp] theorem toCLM_mulHS (B C : HilbertSchmidt H H) :
    toCLM (mulHS B C) = (toCLM B).comp (toCLM C) := rfl

theorem range_le_sup_left_of (B C : HilbertSchmidt H H) :
    LinearMap.range (toCLM (B + C + mulHS B C)).toLinearMap ≤
      LinearMap.range (toCLM B).toLinearMap ⊔ LinearMap.range (toCLM C).toLinearMap := by
  rintro z ⟨x, rfl⟩
  have e : (toCLM (B + C + mulHS B C)).toLinearMap x =
      toCLM B x + toCLM C x + toCLM B (toCLM C x) := by simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left ⟨x, rfl⟩
  · exact Submodule.mem_sup_right ⟨x, rfl⟩
  · exact Submodule.mem_sup_left ⟨toCLM C x, rfl⟩

/-- Finite-rank case of the product identity. -/
theorem det2_product_of_finiteRank (B C : HilbertSchmidt H H)
    (hB : HasFiniteRank (toCLM B)) (hC : HasFiniteRank (toCLM C)) :
    det2 (B + C + mulHS B C) = det2 B * det2 C * Real.exp (-pairTrace B C) := by
  classical
  letI : FiniteDimensional ℝ (LinearMap.range (toCLM B).toLinearMap) := hB
  letI : FiniteDimensional ℝ (LinearMap.range (toCLM C).toLinearMap) := hC
  set V : Submodule ℝ H :=
    LinearMap.range (toCLM B).toLinearMap ⊔ LinearMap.range (toCLM C).toLinearMap
  have hVB : LinearMap.range (toCLM B).toLinearMap ≤ V := le_sup_left
  have hVC : LinearMap.range (toCLM C).toLinearMap ≤ V := le_sup_right
  have hVP := range_le_sup_left_of B C
  have hP : HasFiniteRank (toCLM (B + C + mulHS B C)) :=
    Submodule.finiteDimensional_of_le hVP
  rw [det2_of_finiteRank _ hP, det2_of_finiteRank B hB, det2_of_finiteRank C hC,
    finiteRankDet2_eq_restriction _ hP V hVP, finiteRankDet2_eq_restriction _ hB V hVB,
    finiteRankDet2_eq_restriction _ hC V hVC, pairTrace_eq_trace_restrict B C V hVB hVC]
  have hsplit : restrictedEnd (toCLM (B + C + mulHS B C)).toLinearMap V hVP =
      restrictedEnd (toCLM B).toLinearMap V hVB + restrictedEnd (toCLM C).toLinearMap V hVC +
        restrictedEnd (toCLM B).toLinearMap V hVB * restrictedEnd (toCLM C).toLinearMap V hVC := by
    ext x
    simp [restrictedEnd]
  rw [hsplit]
  exact finiteDet2_product _ _

/-- **G4 product identity** for arbitrary real Hilbert--Schmidt `B, C`. -/
theorem det2_product (B C : HilbertSchmidt H H) :
    det2 (B + C + mulHS B C) = det2 B * det2 C * Real.exp (-pairTrace B C) := by
  have hf : Continuous (fun p : HilbertSchmidt H H × HilbertSchmidt H H =>
      det2 (p.1 + p.2 + mulHS p.1 p.2)) :=
    continuous_det2.comp ((continuous_fst.add continuous_snd).add mulHS.continuous₂)
  have hg : Continuous (fun p : HilbertSchmidt H H × HilbertSchmidt H H =>
      det2 p.1 * det2 p.2 * Real.exp (-pairTrace p.1 p.2)) :=
    ((continuous_det2.comp continuous_fst).mul (continuous_det2.comp continuous_snd)).mul
      (Real.continuous_exp.comp continuous_pairTrace.neg)
  have h := Continuous.ext_on (dense_finiteRankSet.prod dense_finiteRankSet) hf hg
    (fun p hp => det2_product_of_finiteRank p.1 p.2 hp.1 hp.2)
  exact congrFun h (B, C)

/-- **G4, inverse form.** If `(I+B)(I+C) = I` (for HS `B, C`), then
`det₂(I+B) · det₂(I+C) · exp(-tr(BC)) = 1`. -/
theorem det2_mul_det2_inverse (B C : HilbertSchmidt H H)
    (hBC : (ContinuousLinearMap.id ℝ H + toCLM B).comp (ContinuousLinearMap.id ℝ H + toCLM C) =
      ContinuousLinearMap.id ℝ H) :
    det2 B * det2 C * Real.exp (-pairTrace B C) = 1 := by
  have h0 : B + C + mulHS B C = 0 := by
    apply HilbertSchmidt.ext
    intro x
    have hx := congrArg (fun T : H →L[ℝ] H => T x) hBC
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, map_add] at hx
    simp only [toCLM_add, toCLM_mulHS, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, toCLM_zero, ContinuousLinearMap.zero_apply]
    rw [show toCLM B x + toCLM C x + toCLM B (toCLM C x) =
        (x + toCLM B x + (toCLM C x + toCLM B (toCLM C x))) - x by abel, hx, sub_self]
  rw [← det2_product, h0, det2_zero]

/-- **G4 nonvanishing (right inverse).** If `I + B` has a bounded right inverse `R`, then
`det₂(I+B) ≠ 0`.  (The inverse is written `I + C` with `C = -B R`, which is HS by the ideal
property.) -/
theorem det2_ne_zero_of_rightInverse (B : HilbertSchmidt H H) (R : H →L[ℝ] H)
    (hR : (ContinuousLinearMap.id ℝ H + toCLM B).comp R = ContinuousLinearMap.id ℝ H) :
    det2 B ≠ 0 := by
  set C : HilbertSchmidt H H := -precompose B R
  have hC : toCLM C = -(toCLM B).comp R := by simp [C]
  have hBC : (ContinuousLinearMap.id ℝ H + toCLM B).comp
      (ContinuousLinearMap.id ℝ H + toCLM C) = ContinuousLinearMap.id ℝ H := by
    ext x
    have hx := congrArg (fun T : H →L[ℝ] H => T x) hR
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply] at hx
    simp only [hC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, map_add, map_neg]
    have hB := congrArg (toCLM B) hx
    rw [map_add] at hB
    rw [hB, add_neg_cancel_right]
  intro h
  have := det2_mul_det2_inverse B C hBC
  rw [h, zero_mul, zero_mul] at this
  exact zero_ne_one this

/-- **G4 nonvanishing (bounded invertibility).** If `I + B` is a unit in the algebra of bounded
operators, then `det₂(I+B) ≠ 0`. -/
theorem det2_ne_zero_of_isUnit (B : HilbertSchmidt H H)
    (h : IsUnit (1 + toCLM B : H →L[ℝ] H)) : det2 B ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  apply det2_ne_zero_of_rightInverse B (u⁻¹ : (H →L[ℝ] H)ˣ)
  have h1 := u.mul_inv
  rw [hu] at h1
  exact h1

end NlsGge.Analysis.RegularizedDeterminant
