import QuantumNLS.Prop025OTorus
import QuantumNLS.R52CFClassical

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5b-3:
**the frozen affine trajectory is the joint window/action trajectory** (source lines 621-633).

"Thus the joint window/action trajectory solves the frozen affine equation.  Uniqueness for the smooth `L²` vector
field of `F_{a,t,θ}` identifies it with `v_{a,t,θ}` ... This argument uses the equality of vector fields on the
orbit, not equality of their Hessians away from it."  and (lines 650-654) "The simultaneous finite-action phase is
an isometry on every sequence Sobolev space and is identical in the two expressions.  Thus the window-removal proof
of Proposition prop:window applies with that common phase."

We go the other way round (no existence of window flows is assumed or needed): from the frozen affine trajectory
`γ` (`γ(0) = u`, `γ' = X_F(γ)`, the flow consumed by PROP-021) we CONSTRUCT the physical window trajectory
`y(τ) = T_{(1-τ)θ}(γ(τ))` from the rotated datum `T_θ u`, prove it satisfies the printed window equation
`y' = -i∇(Σ_r t_r h_{r,a})(y)` (full real gradient convention, `Prop025OInputs.IsWindowTrajectory`), and
`y(1) = γ(1)`.  The ingredients: the gradient agreement on the whole phase torus (stage O5b-2), the action flows of
the accepted chart (`T_{sθ} = Ψ ∘ rot(sθ) ∘ Φ`, finitely supported `θ`), and the equivariance `E X_f = X_f ∘ T` of
invariant fields under the symplectic differential `E` of `T` (stage O5b-2).
* `Pm`, `Rop`, `Rop_apply`, `hasDerivAt_Rop`: `rot(sθ)` as an explicitly differentiable operator family;
* `physGradient_of`: the DEF-015 gradient realizes the printed `IsPhysGradient`;
* **`window_traj`**: the construction.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal ComplexConjugate InnerProductSpace
open Filter Set Metric

namespace QuantumNLS.Prop025OTraj
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActionTorus (rotate rotate_apply)
open QuantumNLS.SymplecticBracket (hamField omega)
open QuantumNLS.RootMassInvolutionR8 (mass)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
open QuantumNLS.RF535Final (Tact Tθ Hθ GlobalStatement)
open QuantumNLS.Prop025OPhys (rotL rotL_apply)
open QuantumNLS.Prop025OTorus

section Gen
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

/-- The DEF-015 gradient realizes `dF(y)[w] = 2 Re⟪g, w⟫`. -/
theorem physGradient_of (F : H → ℝ) (y : H) (hd : DifferentiableAt ℝ F y) :
    HasFDerivAt F ((2 : ℝ) • (Complex.reCLM.comp ((innerSL ℂ (SymplecticBracket.gradient F y)).restrictScalars ℝ))) y := by
  convert hd.hasFDerivAt using 1
  ext w
  rw [SymplecticBracket.fderiv_eq_two_inner_gradient, real_inner_eq_re_inner]
  simp

end Gen

/-! ### 1. The rotation `rot(sθ)` as an explicitly differentiable operator family -/

/-- The coordinate projection `z ↦ z_m e_m` (`= ½(1 - R_m)`, `R_m` the reflection of the `m`th coordinate). -/
def Pm (m : ℤ) : K →L[ℝ] K :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ K - rotL (Pi.mulSingle m (-1 : Circle)))

theorem Pm_apply (m : ℤ) (z : K) (j : ℤ) : Pm m z j = if j = m then z j else 0 := by
  simp only [Pm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    rotL_apply, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, rotate_apply, Pi.mulSingle_apply]
  split_ifs with h
  · subst h; simp [Circle.coe_neg, Complex.real_smul]; ring
  · simp

/-- `rot(sθ) = 1 + Σ_{m∈F} (e^{-isθ_m} - 1) P_m`. -/
def Rop (F : Finset ℤ) (θ : Linf) (s : ℝ) : K →L[ℝ] K :=
  ContinuousLinearMap.id ℝ K + ∑ m ∈ F, (Complex.exp (-(((s * θ m : ℝ)) : ℂ) * Complex.I) - 1) • Pm m

/-- Its derivative in `s`. -/
def Rop' (F : Finset ℤ) (θ : Linf) (s : ℝ) : K →L[ℝ] K :=
  ∑ m ∈ F, (-((θ m : ℝ) : ℂ) * Complex.I * Complex.exp (-(((s * θ m : ℝ)) : ℂ) * Complex.I)) • Pm m

theorem Rop_apply (F : Finset ℤ) (θ : Linf) (hθ : ∀ m ∉ F, θ m = 0) (s : ℝ) (z : K) :
    Rop F θ s z = R52CFOrbit.rot (s • θ) z := by
  refine lp.ext (funext fun j => ?_)
  rw [R52CFOrbit.rot_apply]
  simp only [Rop, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, lp.coeFn_add, Pi.add_apply,
    lp.coeFn_sum, lp.coeFn_smul, Pm_apply, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hj
  · ring
  · rw [hθ j hj]; simp

theorem hasDerivAt_Rop (F : Finset ℤ) (θ : Linf) (s : ℝ) :
    HasDerivAt (Rop F θ) (Rop' F θ s) s := by
  have he : ∀ m : ℤ, HasDerivAt (fun s : ℝ => Complex.exp (-(((s * θ m : ℝ)) : ℂ) * Complex.I) - 1)
      (-((θ m : ℝ) : ℂ) * Complex.I * Complex.exp (-(((s * θ m : ℝ)) : ℂ) * Complex.I)) s := by
    intro m
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * (-((θ m : ℝ) : ℂ) * Complex.I))
        (1 * (-((θ m : ℝ) : ℂ) * Complex.I)) s := by
      have := (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-((θ m : ℝ) : ℂ) * Complex.I)
      simpa using this
    have h2 := h1.cexp.sub_const 1
    have hf : (fun s : ℝ => Complex.exp ((s : ℂ) * (-((θ m : ℝ) : ℂ) * Complex.I)) - 1) =
        fun s : ℝ => Complex.exp (-(((s * θ m : ℝ)) : ℂ) * Complex.I) - 1 := by
      funext s; congr 2; push_cast; ring
    rw [hf] at h2
    convert h2 using 1
    push_cast; ring
  unfold Rop Rop'
  have hs := HasDerivAt.fun_sum (u := F) (fun m _ => (he m).smul_const (Pm m))
  have h := (hasDerivAt_const s (ContinuousLinearMap.id ℝ K)).add hs
  rw [zero_add] at h
  exact h

theorem Rop_zero (F : Finset ℤ) (θ : Linf) (hθ : ∀ m ∉ F, θ m = 0) (z : K) : Rop F θ 0 z = z := by
  rw [Rop_apply F θ hθ]
  refine lp.ext (funext fun j => ?_)
  rw [R52CFOrbit.rot_apply]
  simp

/-! ### 2. The construction -/

/-- **The joint window/action trajectory.**  For the frozen-contour functional `F` (any differentiable function
invariant under the product torus) whose differential agrees on the phase torus of `u` with
`d(Σ_r t_r h_{r,a}) + Σ_i θ_i dI_{n_i}`, and the finitely supported angle vector `θ` with
`Σ_i θ_i I_{n_i} = H_θ`: the curve `y(τ) = T_{(1-τ)θ}(γ(τ))` is a physical window trajectory from `T_θ u`
(the printed `IsWindowTrajectory`) and `y(1) = γ(1)`. -/
theorem window_traj {κ : ℝ} (hκ : 0 < κ) {L : ℝ} [Fact (0 < L)] {d : ℝ} {Φl : L2T L → K} {Ψl : K → L2T L}
    (hG : GlobalStatement L κ hκ d Φl Ψl) (u : L2T L) (R : Finset ℕ) (t : ℕ → ℝ) (a : ℝ)
    {F : L2T L → ℝ} (hF : ∀ ψ v, F (Tact (L := L) hκ ψ v) = F v) (hFd : Differentiable ℝ F)
    {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (I : Finset ℤ) (θ : Linf) (hθ : ∀ m ∉ I, θ m = 0)
    (hA : ∀ v, ∑ i, θf i * mass hκ (n i) v = Hθ (L := L) hκ θ v)
    (hgr : ∀ ψ : Torus, DifferentiableAt ℝ (Prop025OInputs.windowFamily (L := L) κ R t a) (Tact hκ ψ u) ∧
      fderiv ℝ F (Tact hκ ψ u) = fderiv ℝ (Prop025OInputs.windowFamily (L := L) κ R t a) (Tact hκ ψ u) +
        ∑ i, θf i • fderiv ℝ (mass hκ (n i)) (Tact hκ ψ u))
    (γ : ℝ → L2T L) (hγ0 : γ 0 = u) (hγ : ∀ τ, HasDerivAt γ (hamField F (γ τ)) τ) :
    ∃ y : ℝ → L2T L,
      Prop025OInputs.IsWindowTrajectory (L := L) κ R t a (Tθ (L := L) hκ θ u) y ∧ y 1 = γ 1 := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, hΦa, hΨa, hΨΦ, hΦΨ, -, -, -, hdiff, -, -, -, -, -, hrotθ, -, -⟩ :=
    hG.2
  set W := Prop025OInputs.windowFamily (L := L) κ R t a with hWdef
  set Hf := Hθ (L := L) hκ θ with hHf
  -- the action flows in chart form
  have hTθ : ∀ (s : ℝ) (x : L2T L), Tθ (L := L) hκ (s • θ) x = Ψ (Rop I θ s (Φ x)) := by
    intro s x
    have hΦT : Φ (Tθ (L := L) hκ (s • θ) x) = Rop I θ s (Φ x) := by
      rw [Rop_apply I θ hθ]
      refine lp.ext (funext fun j => ?_)
      rw [hrotθ (s • θ) x j, R52CFOrbit.rot_apply]
    rw [← hΦT, hΨΦ]
  have hTact : ∀ s : ℝ, Tθ (L := L) hκ (s • θ) = Tact (L := L) hκ (fun j => Circle.exp ((s • θ) j)) :=
    fun s => funext fun x => (hG.1.2.1 (s • θ) x).symm
  -- invariance and differentiability of the action Hamiltonian `H_θ`
  have hHsum : Hf = fun v => ∑ m ∈ I, θ m * mass hκ m v := R52CFOrbit.Hθ_eq_sum hκ I θ hθ
  have hHinv : ∀ ψ v, Hf (Tact (L := L) hκ ψ v) = Hf v := by
    intro ψ v; rw [hHsum]
    exact Finset.sum_congr rfl fun m _ => by rw [mass_Tact hκ hG ψ m v]
  have hHd : Differentiable ℝ Hf := fun v => R52CFClassical.differentiableAt_Hθ hκ I θ hθ v
  have hWinv : ∀ ψ v, W (Tact (L := L) hκ ψ v) = W v := fun ψ v => windowFamily_Tact hκ hG ψ R t a v
  -- the trajectory stays on the phase torus
  have htor : ∀ τ, ∃ ψ : Torus, γ τ = Tact (L := L) hκ ψ u := by
    intro τ
    refine on_torus hκ hG (fun m => ?_)
    rw [mass_conserved hκ hG hF hFd γ hγ m τ, hγ0]
  -- the field splits along the trajectory
  have hAfun : (fun v => ∑ i, θf i * mass hκ (n i) v) = Hf := funext hA
  have hsplit : ∀ τ, hamField F (γ τ) = hamField W (γ τ) + hamField Hf (γ τ) := by
    intro τ
    obtain ⟨ψ, hψ⟩ := htor τ
    obtain ⟨hWd, hg⟩ := hgr ψ
    rw [← hψ] at hWd hg
    have := field_split (F := F) (W := W) hκ hWd n θf hg
    rwa [hAfun] at this
  -- the window Hamiltonian is differentiable at every torus point
  have hWtor : ∀ v ψ, v = Tact (L := L) hκ ψ u → DifferentiableAt ℝ W v := by
    rintro v ψ rfl; exact (hgr ψ).1
  -- the curve
  set c : ℝ → K := fun τ => Φ (γ τ) with hc
  have hcd : ∀ τ, HasDerivAt c (fderiv ℝ Φ (γ τ) (hamField F (γ τ))) τ := fun τ =>
    (hΦa (γ τ)).differentiableAt.hasFDerivAt.comp_hasDerivAt τ (hγ τ)
  set Rc : ℝ → K := fun τ => Rop I θ (1 - τ) (c τ) with hRc
  have hRd : ∀ τ, HasDerivAt Rc (((-Rop' I θ (1 - τ)) (c τ)) +
      Rop I θ (1 - τ) (fderiv ℝ Φ (γ τ) (hamField F (γ τ)))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => Rop I θ (1 - τ)) (-Rop' I θ (1 - τ)) τ := by
      have := (hasDerivAt_Rop I θ (1 - τ)).scomp τ ((hasDerivAt_id τ).const_sub 1)
      rw [neg_one_smul] at this
      exact this
    exact h1.clm_apply (hcd τ)
  set y : ℝ → L2T L := fun τ => Ψ (Rc τ) with hy
  have hyT : ∀ τ, y τ = Tθ (L := L) hκ ((1 - τ) • θ) (γ τ) := fun τ => by
    simp only [hy, hRc, hc]; rw [hTθ]
  have hyd : ∀ τ, HasDerivAt y (fderiv ℝ Ψ (Rc τ) (((-Rop' I θ (1 - τ)) (c τ)) +
      Rop I θ (1 - τ) (fderiv ℝ Φ (γ τ) (hamField F (γ τ))))) τ := fun τ =>
    (hΨa (Rc τ)).differentiableAt.hasFDerivAt.comp_hasDerivAt τ (hRd τ)
  -- identification of the derivative
  have hyX : ∀ τ, fderiv ℝ Ψ (Rc τ) (((-Rop' I θ (1 - τ)) (c τ)) +
      Rop I θ (1 - τ) (fderiv ℝ Φ (γ τ) (hamField F (γ τ)))) = hamField W (y τ) := by
    intro τ
    set s : ℝ := 1 - τ with hs
    set x : L2T L := γ τ with hx
    set ψs : Torus := fun j => Circle.exp ((s • θ) j) with hψs
    have hTs : Tθ (L := L) hκ (s • θ) = Tact (L := L) hκ ψs := hTact s
    have hyx : y τ = Tact (L := L) hκ ψs x := by rw [hyT, ← hTs]
    -- the `s`-partial: the action field
    have hpart : fderiv ℝ Ψ (Rc τ) (Rop' I θ s (c τ)) = hamField Hf (y τ) := by
      obtain ⟨γx, hγx0, hγx, -, -⟩ := hG.1.1 θ x
      have hflow : ∀ σ, γx σ = Tθ (L := L) hκ (σ • θ) x :=
        R52CFClassical.flow_scaling hκ hG I θ hθ x γx hγx0 hγx
      have h1 : HasDerivAt (fun σ => Tθ (L := L) hκ (σ • θ) x) (hamField Hf (Tθ (L := L) hκ (s • θ) x)) s := by
        have := hγx s
        rw [hflow s] at this
        have hfun : γx = fun σ => Tθ (L := L) hκ (σ • θ) x := funext hflow
        rw [hfun] at this
        exact this
      have h2 : HasDerivAt (fun σ => Tθ (L := L) hκ (σ • θ) x)
          (fderiv ℝ Ψ (Rop I θ s (Φ x)) (Rop' I θ s (Φ x))) s := by
        have hfun : (fun σ => Tθ (L := L) hκ (σ • θ) x) = fun σ => Ψ (Rop I θ σ (Φ x)) :=
          funext fun σ => hTθ σ x
        rw [hfun]
        exact (hΨa _).differentiableAt.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_Rop I θ s).clm_apply
          (hasDerivAt_const s (Φ x)))
          |>.congr_deriv (by simp)
      have := h2.unique h1
      rw [hyT]
      exact this
    -- the `x`-partial: the differential `E` of `T_{sθ}`
    have hEd : HasFDerivAt (Tact (L := L) hκ ψs)
        ((fderiv ℝ Ψ (Rop I θ s (Φ x))).comp ((Rop I θ s).comp (fderiv ℝ Φ x))) x := by
      have hfun : (fun x' => Ψ (Rop I θ s (Φ x'))) = Tact (L := L) hκ ψs := by
        funext x'; rw [← hTθ s x', hTs]
      have := (hΨa _).differentiableAt.hasFDerivAt.comp x
        ((Rop I θ s).hasFDerivAt.comp x (hΦa x).differentiableAt.hasFDerivAt)
      rw [← hfun]
      exact this
    obtain ⟨E0, hE0, hsurj, hsymp⟩ := Tact_deriv hκ hG ψs x
    have hEE := hEd.unique hE0
    set E := (fderiv ℝ Ψ (Rop I θ s (Φ x))).comp ((Rop I θ s).comp (fderiv ℝ Φ x)) with hEdef
    have hyP : Tact (L := L) hκ ψs x = Tact (L := L) hκ ψs (Tact (L := L) hκ (Classical.choose (htor τ)) u) := by
      rw [← Classical.choose_spec (htor τ)]
    have hWy : DifferentiableAt ℝ W (Tact (L := L) hκ ψs x) := by
      rw [hyP, ← hG.1.2.2.1]
      exact (hgr _).1
    have hEW : E (hamField W x) = hamField W (Tact (L := L) hκ ψs x) := by
      rw [hEE]
      exact hamField_equiv hκ ψs (hWinv ψs) hWy hE0 hsurj hsymp
    have hEH : E (hamField Hf x) = hamField Hf (Tact (L := L) hκ ψs x) := by
      rw [hEE]
      exact hamField_equiv hκ ψs (hHinv ψs) (hHd _) hE0 hsurj hsymp
    have hEF : fderiv ℝ Ψ (Rc τ) (Rop I θ s (fderiv ℝ Φ x (hamField F x))) =
        E (hamField F x) := rfl
    rw [map_add, ContinuousLinearMap.neg_apply, map_neg, hpart, hEF, hsplit τ, map_add, hEW, hEH, ← hyx]
    abel
  refine ⟨y, ⟨?_, fun τ _ => ?_⟩, ?_⟩
  · rw [hyT, hγ0, sub_zero, one_smul]
  · obtain ⟨ψ, hψ⟩ := htor τ
    have hyψ : y τ = Tact (L := L) hκ ((fun j => Circle.exp (((1 - τ) • θ) j)) * ψ) u := by
      rw [hyT, hTact, hψ, hG.1.2.2.1]
    have hWy : DifferentiableAt ℝ W (y τ) := hWtor _ _ hyψ
    refine ⟨SymplecticBracket.gradient W (y τ), physGradient_of W (y τ) hWy, ?_⟩
    have := (hyd τ).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
    rw [hyX τ] at this
    exact this
  · simp only [hy, hRc, sub_self]
    rw [Rop_zero I θ hθ, hc, hΨΦ]

end QuantumNLS.Prop025OTraj

#print axioms QuantumNLS.Prop025OTraj.physGradient_of
#print axioms QuantumNLS.Prop025OTraj.window_traj
-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OTraj." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OTraj aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
