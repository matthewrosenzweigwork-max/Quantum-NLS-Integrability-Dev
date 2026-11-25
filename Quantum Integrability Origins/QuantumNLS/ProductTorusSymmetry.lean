import QuantumNLS.ProductTorusPrimitive

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T7c: covariance of `ᾱ` under unitary and antiunitary symmetries
# permuting the actions

Source: `chapters/global/product_torus.tex`, theorem statement, last sentence ("More generally, every linear unitary or
antiunitary symmetry that permutes the `I_n` has the corresponding covariance of `ᾱ`"), and the end of the proof
("A unitary symmetry permuting the actions conjugates the product action by the same permutation; an antiunitary
symmetry also reverses the angles. These transformations preserve product Haar measure. The identical calculation
proves the final covariance assertion.").

Setting: `U : 𝓗 →L[ℝ] 𝓗` with a right inverse `V` (`U (V v) = v`), `ω(Ua, Ub) = ε ω(a,b)` with `ε = 1` (unitary) or
`ε = −1` (antiunitary), and `I_n(Uu) = I_{σ n}(u)` for a permutation `σ` of `ℤ`.

Proved (T7a hypotheses `PHyp`):
* `pair_perm`, `DI_U`, `X_U` (`X_θ(Uv) = ε U X_{θ∘σ⁻¹}(v)`), `flow_U` (`φ_θ^t(Uu) = U φ_{θ∘σ⁻¹}^{εt}(u)`);
* `twist σ ε ψ` (the permuted torus element, inverted when `ε = −1`), `act_U` (`T_ψ U = U T_{twist ψ}`),
  `integral_twist` (B6 `coordinatePermutation_haar`, `inversion_haar`);
* **`alphaBar_U`**: `ᾱ_{Uu}(Uh) = ε ᾱ_u(h)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace QuantumNLS.ProductTorusSymmetry

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute QuantumNLS.ProductTorusContinuity QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusFixedVector QuantumNLS.ProductTorusPrimitive
open QuantumNLS.Ext025B6TorusCoordinates (Torus inversion_haar coordinatePermutation coordinatePermutation_haar)
open QuantumNLS.Ext025BHaar (productCircleHaar)

/-- The permuted angle sequence `θ ∘ σ⁻¹`. -/
def permLinf (σ : ℤ ≃ ℤ) (θ : Linf) : Linf :=
  ⟨fun m => θ (σ.symm m), memℓp_infty ⟨‖θ‖, by
    rintro _ ⟨m, rfl⟩
    exact lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero θ (σ.symm m)⟩⟩

theorem permLinf_apply (σ : ℤ ≃ ℤ) (θ : Linf) (m : ℤ) : permLinf σ θ m = θ (σ.symm m) := rfl

theorem pair_perm (σ : ℤ ≃ ℤ) (θ : Linf) (x y : L1 ℝ) (hxy : ∀ n, y n = x (σ n)) :
    pair θ y = pair (permLinf σ θ) x := by
  rw [pair_apply, pair_apply]
  calc ∑' n, θ n * y n = ∑' n, permLinf σ θ (σ n) * x (σ n) :=
        tsum_congr fun n => by rw [hxy, permLinf_apply, Equiv.symm_apply_apply]
    _ = ∑' m, permLinf σ θ m * x m := Equiv.tsum_eq σ (fun m => permLinf σ θ m * x m)

/-- The permuted (and, for `ε ≠ 1`, inverted) torus element. -/
def twist (σ : ℤ ≃ ℤ) (ε : ℝ) (ψ : Torus) : Torus :=
  if ε = 1 then coordinatePermutation σ.symm ψ else (coordinatePermutation σ.symm ψ)⁻¹

theorem integral_twist (σ : ℤ ≃ ℤ) (ε : ℝ) (f : Torus → ℝ) :
    ∫ ψ, f (twist σ ε ψ) ∂productCircleHaar = ∫ ψ, f ψ ∂productCircleHaar := by
  unfold twist
  by_cases hε : ε = 1
  · simp only [ite_eq_left hε]
    exact (coordinatePermutation_haar σ.symm).integral_comp
      (coordinatePermutation σ.symm).toHomeomorph.measurableEmbedding f
  · simp only [ite_eq_right hε]
    exact (inversion_haar.comp (coordinatePermutation_haar σ.symm)).integral_comp
      ((MeasurableEquiv.inv Torus).measurableEmbedding.comp
        (coordinatePermutation σ.symm).toHomeomorph.measurableEmbedding) f

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

theorem omega_smul_left (c : ℝ) (a k : E) : omega (c • a) k = c * omega a k := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := E)
  have hom : ∀ x y, omega x y = J x y := fun x y => (hJ x y).symm
  rw [hom, hom, map_smul]
  rfl

section Symmetry

variable {U V : E →L[ℝ] E} {σ : ℤ ≃ ℤ} {ε : ℝ}

theorem DI_U (H : PHyp I DI) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (v k : E) (n : ℤ) :
    (DI (U v) (U k) : ℤ → ℝ) n = (DI v k : ℤ → ℝ) (σ n) := by
  have h1 : HasFDerivAt (fun y => coord n (I (U y))) ((coord n).comp ((DI (U v)).comp U)) v :=
    (coord n).hasFDerivAt.comp v ((H.hyp.hasFDerivAt (U v)).comp v U.hasFDerivAt)
  have h2 : HasFDerivAt (fun y => coord n (I (U y))) ((coord (σ n)).comp (DI v)) v := by
    have : (fun y => coord n (I (U y))) = fun y => coord (σ n) (I y) :=
      funext fun y => by rw [coord_apply, coord_apply, hUI]
    rw [this]
    exact (coord (σ n)).hasFDerivAt.comp v (H.hyp.hasFDerivAt v)
  have := congrArg (fun L : E →L[ℝ] ℝ => L k) (h1.unique h2)
  simpa only [ContinuousLinearMap.comp_apply, coord_apply] using this

/-- `X_θ(Uv) = ε U X_{θ∘σ⁻¹}(v)`. -/
theorem X_U (H : PHyp I DI) (hUV : ∀ v, U (V v) = v) (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b)
    (hε : ε = 1 ∨ ε = -1) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (θ : Linf) (v : E) :
    X DI θ (U v) = ε • U (X DI (permLinf σ θ) v) := by
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  refine sub_eq_zero.1 (omega_nondeg fun k => ?_)
  rw [omega_sub_left, omega_smul_left, omega_X]
  have e1 : pair θ (DI (U v) k) = pair (permLinf σ θ) (DI v (V k)) := by
    apply pair_perm
    intro n
    have := DI_U H hUI v (V k) n
    rwa [hUV] at this
  have e2 : omega (U (X DI (permLinf σ θ) v)) k = ε * pair (permLinf σ θ) (DI v (V k)) := by
    have := hUω (X DI (permLinf σ θ) v) (V k)
    rwa [hUV, omega_X] at this
  rw [e1, e2]
  linear_combination (-pair (permLinf σ θ) (DI v (V k))) * hεε

/-- `φ_θ^t(Uu) = U φ_{θ∘σ⁻¹}^{εt}(u)`. -/
theorem flow_U (H : PHyp I DI) (hUV : ∀ v, U (V v) = v) (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b)
    (hε : ε = 1 ∨ ε = -1) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (θ : Linf) (u : E) (t : ℝ) :
    flow DI θ t (U u) = U (flow DI (permLinf σ θ) (ε * t) u) := by
  have hα : ∀ s, HasDerivAt (fun s => U (flow DI (permLinf σ θ) (ε * s) u))
      (X DI θ (U (flow DI (permLinf σ θ) (ε * s) u))) s := by
    intro s
    have h0 : HasDerivAt (fun s : ℝ => ε * s) ε s := by simpa using (hasDerivAt_id s).const_mul ε
    have h1 := (hasDerivAt_flow H.hyp (permLinf σ θ) u (ε * s)).scomp s h0
    have h2 := U.hasFDerivAt.comp_hasDerivAt s h1
    rw [X_U H hUV hUω hε hUI, ← U.map_smul]
    exact h2
  exact flow_eq_of_sol H.hyp θ (α := fun s => U (flow DI (permLinf σ θ) (ε * s) u))
    (by simp [flow_zero H.hyp]) hα t

theorem act_twist (H : PHyp I DI) (hε : ε = 1 ∨ ε = -1) (ψ : Torus) :
    act DI (twist σ ε ψ) = T DI (ε • permLinf σ (lift ψ)) :=
  act_eq_T H.hyp H.nonneg H.proper H.periodic (fun n => by
    unfold twist
    rcases hε with h1 | h1
    · rw [ite_eq_left h1, h1, one_smul, permLinf_apply]
      exact exp_lift ψ (σ.symm n)
    · rw [ite_eq_right (by rw [h1]; norm_num), h1, neg_smul, one_smul, lp.coeFn_neg, Pi.neg_apply, permLinf_apply,
        Circle.exp_neg]
      exact congrArg Inv.inv (exp_lift ψ (σ.symm n)))

/-- `T_ψ U = U T_{twist ψ}`. -/
theorem act_U (H : PHyp I DI) (hUV : ∀ v, U (V v) = v) (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b)
    (hε : ε = 1 ∨ ε = -1) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (ψ : Torus) (u : E) :
    act DI ψ (U u) = U (act DI (twist σ ε ψ) u) := by
  rw [act_twist H hε ψ]
  show flow DI (lift ψ) 1 (U u) = U (flow DI (ε • permLinf σ (lift ψ)) 1 u)
  rw [flow_U H hUV hUω hε hUI, flow_smul H.hyp]

theorem fderiv_act_U (H : PHyp I DI) (hUV : ∀ v, U (V v) = v) (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b)
    (hε : ε = 1 ∨ ε = -1) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (ψ : Torus) (u h : E) :
    fderiv ℝ (act DI ψ) (U u) (U h) = U (fderiv ℝ (act DI (twist σ ε ψ)) u h) := by
  have hfun : act DI ψ ∘ U = U ∘ act DI (twist σ ε ψ) := funext fun v => act_U H hUV hUω hε hUI ψ v
  have h1 : fderiv ℝ (act DI ψ ∘ U) u = (fderiv ℝ (act DI ψ) (U u)).comp U := by
    rw [fderiv_comp u (hasFDerivAt_act H ψ (U u)).differentiableAt U.differentiableAt, U.fderiv]
  have h2 : fderiv ℝ (U ∘ act DI (twist σ ε ψ)) u = U.comp (fderiv ℝ (act DI (twist σ ε ψ)) u) := by
    rw [fderiv_comp u U.differentiableAt (hasFDerivAt_act H _ u).differentiableAt, U.fderiv]
  have := congrArg (fun L : E →L[ℝ] E => L h) (h1.symm.trans ((congrArg (fun f => fderiv ℝ f u) hfun).trans h2))
  simpa using this

omit [CompleteSpace E] in
theorem alpha_U (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b) (a b : E) : alpha (U a) (U b) = ε * alpha a b := by
  rw [alpha_eq, alpha_eq, hUω]
  ring

/-- **Covariance of `ᾱ`**: `ᾱ_{Uu}(Uh) = ε ᾱ_u(h)` for a unitary (`ε = 1`) or antiunitary (`ε = −1`) symmetry
permuting the actions. -/
theorem alphaBar_U (H : PHyp I DI) (hUV : ∀ v, U (V v) = v) (hUω : ∀ a b, omega (U a) (U b) = ε * omega a b)
    (hε : ε = 1 ∨ ε = -1) (hUI : ∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) (u h : E) :
    alphaBar DI (U u) (U h) = ε * alphaBar DI u h := by
  unfold alphaBar
  have key : ∀ ψ : Torus, alpha (act DI ψ (U u)) (fderiv ℝ (act DI ψ) (U u) (U h)) =
      ε * alpha (act DI (twist σ ε ψ) u) (fderiv ℝ (act DI (twist σ ε ψ)) u h) := by
    intro ψ
    rw [act_U H hUV hUω hε hUI, fderiv_act_U H hUV hUω hε hUI, alpha_U hUω]
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact integral_twist σ ε (fun ψ => alpha (act DI ψ u) (fderiv ℝ (act DI ψ) u h))

end Symmetry

end QuantumNLS.ProductTorusSymmetry

#print axioms QuantumNLS.ProductTorusSymmetry.integral_twist
#print axioms QuantumNLS.ProductTorusSymmetry.X_U
#print axioms QuantumNLS.ProductTorusSymmetry.flow_U
#print axioms QuantumNLS.ProductTorusSymmetry.act_U
#print axioms QuantumNLS.ProductTorusSymmetry.alphaBar_U
