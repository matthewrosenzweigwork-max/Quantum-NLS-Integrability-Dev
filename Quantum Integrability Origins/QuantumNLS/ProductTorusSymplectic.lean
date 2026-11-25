import QuantumNLS.ProductTorusCommute

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T5a: strong symplecticity

Source: `chapters/global/product_torus.tex`, proof, "Bounded angle generators and complete flows", fifth paragraph:
"For any `h,k`, the full variational equation and `ω(DX_θ a, b) = d²H_θ[a,b]` show that
`ω(Dφ_θ^t h, Dφ_θ^t k)` has zero derivative in `t`. Symmetry of the bounded full Hessian gives the cancellation.
Thus each `T_θ` is strongly symplectic. Its inverse and its bounded inverse differential follow from `T_{-θ}`."

Proved (hypotheses `ProductTorusFlow.Hyp`):
* `omega_fderiv_X_symm`: `ω(DX_θ(u)a, b) = ω(DX_θ(u)b, a)` (symmetric Hessian `d²H_θ`);
* `omega_A`: `ω(DX_θ a, b) + ω(a, DX_θ b) = 0`;
* **`symplectic`**: `ω(Dφ_θ^t(u)h, Dφ_θ^t(u)k) = ω(h,k)` for all `t, u, h, k` (derivative of the bounded bilinear
  form along the variational equation, with `ω` realized by the accepted GP-06 isomorphism);
* **`T_symplectic`**: `ω(DT_θ(u)h, DT_θ(u)k) = ω(h,k)`, together with the bounded inverse differential
  `DT_{-θ}(T_θ u)` (two-sided inverse, T2d `derivative_bound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusSymplectic

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

theorem omega_fderiv_X_symm (h : Hyp I DI) (θ : Linf) (u a b : E) :
    omega (fderiv ℝ (X DI θ) u a) b = omega (fderiv ℝ (X DI θ) u b) a := by
  rw [omega_fderiv_X h, omega_fderiv_X h, symm2 h]

theorem omega_A (h : Hyp I DI) (θ : Linf) (u a b : E) :
    omega (fderiv ℝ (X DI θ) u a) b + omega a (fderiv ℝ (X DI θ) u b) = 0 := by
  rw [omega_antisymm a, omega_fderiv_X_symm h θ u a b]
  ring

/-- **Each `φ_θ^t` is strongly symplectic.** -/
theorem symplectic (h : Hyp I DI) (θ : Linf) (t : ℝ) (u a b : E) :
    omega (fderiv ℝ (flow DI θ t) u a) (fderiv ℝ (flow DI θ t) u b) = omega a b := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := E)
  have hom : ∀ v w, omega v w = J v w := fun v w => (hJ v w).symm
  have hg : ∀ s, HasDerivAt (fun s => J (fderiv ℝ (flow DI θ s) u a) (fderiv ℝ (flow DI θ s) u b)) 0 s := by
    intro s
    have ha := hasDerivAt_fderiv_flow_apply h θ u a s
    have hb := hasDerivAt_fderiv_flow_apply h θ u b s
    have hJa := (J : E →L[ℝ] (E →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt s ha
    have hd := hJa.clm_apply hb
    have e : J (fderiv ℝ (X DI θ) (flow DI θ s u) (fderiv ℝ (flow DI θ s) u a)) (fderiv ℝ (flow DI θ s) u b) +
        J (fderiv ℝ (flow DI θ s) u a) (fderiv ℝ (X DI θ) (flow DI θ s u) (fderiv ℝ (flow DI θ s) u b)) = 0 := by
      rw [← hom, ← hom]
      exact omega_A h θ _ _ _
    rw [← e]
    exact hd
  have hc := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  rw [hom, hom]
  refine hc.trans ?_
  show J (fderiv ℝ (flow DI θ 0) u a) (fderiv ℝ (flow DI θ 0) u b) = J a b
  rw [fderiv_flow_zero h]
  rfl

/-- **`T_θ` is a strong symplectic map with bounded inverse differential `DT_{-θ}(T_θ u)`.** -/
theorem T_symplectic (h : Hyp I DI) (θ : Linf) (u : E) :
    (∀ a b, omega (fderiv ℝ (T DI θ) u a) (fderiv ℝ (T DI θ) u b) = omega a b) ∧
      (fderiv ℝ (T DI (-θ)) (T DI θ u)).comp (fderiv ℝ (T DI θ) u) = ContinuousLinearMap.id ℝ E ∧
      (fderiv ℝ (T DI θ) u).comp (fderiv ℝ (T DI (-θ)) (T DI θ u)) = ContinuousLinearMap.id ℝ E ∧
      (∀ v, T DI (-θ) (T DI θ v) = v) ∧ (∀ v, T DI θ (T DI (-θ) v) = v) := by
  refine ⟨fun a b => symplectic h θ 1 u a b, ?_, ?_, T_neg_T h θ, T_T_neg h θ⟩
  · have := fderiv_flow_neg_comp h θ 1 u
    unfold T
    rwa [flow_neg_time h θ 1] at this
  · have := fderiv_flow_neg_comp h (-θ) 1 (T DI θ u)
    unfold T at this ⊢
    rw [flow_neg_time h (-θ) 1, neg_neg] at this
    have hTT : flow DI (-θ) 1 (flow DI θ 1 u) = u := T_neg_T h θ u
    rwa [hTT] at this

end QuantumNLS.ProductTorusSymplectic

#print axioms QuantumNLS.ProductTorusSymplectic.omega_A
#print axioms QuantumNLS.ProductTorusSymplectic.symplectic
#print axioms QuantumNLS.ProductTorusSymplectic.T_symplectic
