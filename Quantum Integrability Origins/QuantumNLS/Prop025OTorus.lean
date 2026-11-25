import QuantumNLS.Prop025OGrad
import QuantumNLS.Prop025OPhys

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5b-2:
**the joint trajectory stays on the full phase torus, and the gradient agreement holds at every point of it**
(source lines 609-627).

"All higher-window and action Hamiltonians preserve every quantum-derived action.  Their joint trajectory from `u`
therefore remains on the same full phase torus and has the same discriminant at every point.  At each point of
that trajectory, eq:MP-window-gradient--eq:MP-action-gradient give eq:MP-full-gradient-agreement as full real
physical differentials."

Data: the accepted global chart statement `RF535Final.GlobalStatement` (R-F5355ABD: `Φ`, `Ψ = Φ⁻¹`, strong
symplecticity, `Φ(T_ψ v) = rotate ψ⁻¹ (Φ v)`, the circle flows of the actions).
* `Tact_deriv`: every torus map `T_ψ` is differentiable with a SURJECTIVE, SYMPLECTIC differential;
* `fderiv_inv`, `hamField_equiv`: a `T_ψ`-invariant function has `dF(v) = dF(T_ψ v) ∘ E` and
  `E X_F(v) = X_F(T_ψ v)`;
* `mass_Tact`, `windowFamily_Tact`: the actions and the full-mass window Hamiltonians are `T_ψ`-invariant (the
  latter by the accepted scalar uniqueness, the measure depends only on the actions);
* `mass_conserved`: a trajectory of the Hamiltonian field of a differentiable `T_ψ`-invariant function conserves
  every action (`{I_n, F} = -dF[X_{I_n}] = 0`, the circle flow of `I_n` is a torus map);
* `on_torus`: equal actions means equal phase torus, `v = T_ψ u`;
* **`grad_transport`**: the gradient agreement at `u` (stage O5b-1 `grad_at`) holds verbatim at every `T_ψ u`,
  and the window Hamiltonian is differentiable there;
* **`field_split`**: on the torus, `X_F = X_{Σ t_r h_{r,a}} + X_{Σ θ_i I_{n_i}}`.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal ComplexConjugate InnerProductSpace
open Filter Set Metric

namespace QuantumNLS.Prop025OTorus
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActionTorus (rotate rotate_apply rotate_mul rotate_one)
open QuantumNLS.SymplecticBracket (hamField omega)
open QuantumNLS.RootMassInvolutionR8 (mass)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
open QuantumNLS.RF535Final (Tact GlobalStatement Iact)
open QuantumNLS.Prop025OPhys (rotL rotL_apply inner_rotate omega_hamField' omega_ext')

section Gen
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

/-- Additivity of the Hamiltonian field in the differential (DEF-015 instance conventions). -/
theorem hamField_add_of {F W M : H → ℝ} {y : H} (h : fderiv ℝ F y = fderiv ℝ W y + fderiv ℝ M y) :
    hamField F y = hamField W y + hamField M y := by
  unfold hamField SymplecticBracket.gradient
  rw [h, map_add, smul_add, smul_add]

end Gen

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} {d : ℝ} {Φl : L2T L → K} {Ψl : K → L2T L}

theorem Tact_one_mul (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (ψ : Torus) (v : L2T L) :
    Tact (L := L) hκ ψ⁻¹ (Tact hκ ψ v) = v := by
  rw [← hG.1.2.2.1, inv_mul_cancel, hG.1.2.2.2.1]

/-- `T_ψ` is differentiable with a surjective symplectic differential. -/
theorem Tact_deriv (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (ψ : Torus) (x : L2T L) :
    ∃ E : L2T L →L[ℝ] L2T L, HasFDerivAt (Tact (L := L) hκ ψ) E x ∧ Function.Surjective E ∧
      ∀ a b, omega (E a) (E b) = omega a b := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, -, -, hΨΦ, hΦΨ, -, -, hsymp, hdiff, -, -, -, -, hrotψ, -, -, -⟩ :=
    hG.2
  set y := Tact (L := L) hκ ψ x with hy
  have hT : ∀ v, Tact (L := L) hκ ψ v = Ψ (rotate ψ⁻¹ (Φ v)) := fun v => by rw [← hrotψ ψ v, hΨΦ]
  obtain ⟨e1, he1, -⟩ := hdiff x
  obtain ⟨e2, he2, he2'⟩ := hdiff y
  have hΦy : Φ y = rotate ψ⁻¹ (Φ x) := hrotψ ψ x
  rw [hΦy] at he2'
  have hcomp := he2'.comp x ((rotL ψ⁻¹).hasFDerivAt.comp x he1)
  have hfun : (Ψ ∘ (rotL ψ⁻¹ ∘ Φ)) = Tact (L := L) hκ ψ := funext fun v => (hT v).symm
  rw [hfun] at hcomp
  refine ⟨_, hcomp, ?_, ?_⟩
  · intro k
    refine ⟨e1.symm (rotL ψ (e2 k)), ?_⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, rotL_apply]
    rw [← rotate_mul, inv_mul_cancel, rotate_one, ContinuousLinearEquiv.symm_apply_apply]
  · intro a b
    have h1 := hsymp y ((((e2.symm : K →L[ℝ] L2T L).comp ((rotL ψ⁻¹).comp (e1 : L2T L →L[ℝ] K)))) a)
      ((((e2.symm : K →L[ℝ] L2T L).comp ((rotL ψ⁻¹).comp (e1 : L2T L →L[ℝ] K)))) b)
    have h2 := hsymp x a b
    rw [he2.fderiv] at h1
    rw [he1.fderiv] at h2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, rotL_apply, inner_rotate] at h1 h2 ⊢
    unfold omega
    linarith

/-- The differential of a `T_ψ`-invariant function. -/
theorem fderiv_inv (hκ : 0 < κ) (ψ : Torus) {f : L2T L → ℝ}
    (hf : ∀ v, f (Tact (L := L) hκ ψ v) = f v) {x : L2T L}
    (hy : DifferentiableAt ℝ f (Tact (L := L) hκ ψ x)) {E : L2T L →L[ℝ] L2T L}
    (hE : HasFDerivAt (Tact (L := L) hκ ψ) E x) :
    HasFDerivAt f ((fderiv ℝ f (Tact (L := L) hκ ψ x)).comp E) x := by
  have hc := hy.hasFDerivAt.comp x hE
  have : f ∘ Tact (L := L) hκ ψ = f := funext hf
  rwa [this] at hc

/-- Equivariance of the Hamiltonian field of a `T_ψ`-invariant function. -/
theorem hamField_equiv (hκ : 0 < κ) (ψ : Torus) {f : L2T L → ℝ}
    (hf : ∀ v, f (Tact (L := L) hκ ψ v) = f v) {x : L2T L}
    (hy : DifferentiableAt ℝ f (Tact (L := L) hκ ψ x)) {E : L2T L →L[ℝ] L2T L}
    (hE : HasFDerivAt (Tact (L := L) hκ ψ) E x) (hs : Function.Surjective E)
    (hω : ∀ a b, omega (E a) (E b) = omega a b) :
    E (hamField f x) = hamField f (Tact (L := L) hκ ψ x) := by
  have hd := fderiv_inv hκ ψ hf hy hE
  apply omega_ext'
  intro k
  obtain ⟨k', rfl⟩ := hs k
  rw [hω]
  calc omega (hamField f x) k' = fderiv ℝ f x k' := omega_hamField' f x k'
    _ = (fderiv ℝ f (Tact (L := L) hκ ψ x)).comp E k' := by rw [hd.fderiv]
    _ = fderiv ℝ f (Tact (L := L) hκ ψ x) (E k') := rfl
    _ = omega (hamField f (Tact (L := L) hκ ψ x)) (E k') := (omega_hamField' f _ _).symm

/-- The actions are invariant under the product torus. -/
theorem mass_Tact (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (ψ : Torus) (n : ℤ) (v : L2T L) :
    mass hκ n (Tact (L := L) hκ ψ v) = mass hκ n v := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, -, -, -, -, hmass, -, -, -, -, -, -, -, hrotψ, -, -, -⟩ := hG.2
  change (RootIndexedMasses.masses hκ (Tact (L := L) hκ ψ v)).1 n = (RootIndexedMasses.masses hκ v).1 n
  rw [← hmass, ← hmass, hrotψ, rotate_apply, norm_mul, Circle.norm_coe, one_mul]

/-- The full-mass window Hamiltonians are invariant under the product torus. -/
theorem windowFamily_Tact (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) (ψ : Torus) (R : Finset ℕ)
    (t : ℕ → ℝ) (a : ℝ) (v : L2T L) :
    Prop025OInputs.windowFamily (L := L) κ R t a (Tact (L := L) hκ ψ v) =
      Prop025OInputs.windowFamily (L := L) κ R t a v := by
  have hm : FullMass.Mmeas κ (Tact (L := L) hκ ψ v) = FullMass.Mmeas κ v := by
    rw [← PhysicalL2Normalization.measure_eq_Mmeas hκ, ← PhysicalL2Normalization.measure_eq_Mmeas hκ]
    exact (HierarchyInputR25m.scalar_uniqueness (L := L) hκ).1 _ _ (fun n => mass_Tact hκ hG ψ n v)
  unfold Prop025OInputs.windowFamily Prop025OInputs.windowHam
  rw [hm]

/-- The derivative of a `T_ψ`-invariant differentiable function vanishes on the field of every action. -/
theorem fderiv_hamField_mass (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) {F : L2T L → ℝ}
    (hF : ∀ ψ v, F (Tact (L := L) hκ ψ v) = F v) (hFd : Differentiable ℝ F) (n : ℤ) (x : L2T L) :
    fderiv ℝ F x (hamField (mass hκ n) x) = 0 := by
  have hc := hG.1.2.2.2.2.2 n x 0
  have h0 : Tact (L := L) hκ (Pi.mulSingle n (Circle.exp 0)) x = x := by
    rw [Circle.exp_zero, Pi.mulSingle_one, hG.1.2.2.2.1]
  have hFc := (hFd (Tact (L := L) hκ (Pi.mulSingle n (Circle.exp 0)) x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  rw [h0] at hFc
  have hconst : (F ∘ fun s : ℝ => Tact (L := L) hκ (Pi.mulSingle n (Circle.exp s)) x) = fun _ => F x :=
    funext fun s => hF _ x
  rw [hconst] at hFc
  have := hFc.unique (hasDerivAt_const (0 : ℝ) (F x))
  exact this

/-- **Action conservation** along a trajectory of the Hamiltonian field of an invariant function. -/
theorem mass_conserved (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) {F : L2T L → ℝ}
    (hF : ∀ ψ v, F (Tact (L := L) hκ ψ v) = F v) (hFd : Differentiable ℝ F) (γ : ℝ → L2T L)
    (hγ : ∀ τ, HasDerivAt γ (hamField F (γ τ)) τ) (n : ℤ) (τ : ℝ) :
    mass hκ n (γ τ) = mass hκ n (γ 0) := by
  have hd : ∀ σ, HasDerivAt (fun σ => mass hκ n (γ σ)) 0 σ := by
    intro σ
    have h1 := (R52CFOrbit.differentiableAt_mass hκ n (γ σ)).hasFDerivAt.comp_hasDerivAt σ (hγ σ)
    have h2 : fderiv ℝ (mass hκ n) (γ σ) (hamField F (γ σ)) = 0 := by
      have e1 : omega (hamField (mass hκ n) (γ σ)) (hamField F (γ σ)) =
          fderiv ℝ (mass hκ n) (γ σ) (hamField F (γ σ)) := omega_hamField' _ _ _
      have e2 : omega (hamField F (γ σ)) (hamField (mass hκ n) (γ σ)) =
          fderiv ℝ F (γ σ) (hamField (mass hκ n) (γ σ)) := omega_hamField' _ _ _
      have e3 : fderiv ℝ F (γ σ) (hamField (mass hκ n) (γ σ)) = 0 :=
        fderiv_hamField_mass hκ hG hF hFd n (γ σ)
      have ha : omega (hamField (mass hκ n) (γ σ)) (hamField F (γ σ)) =
          -omega (hamField F (γ σ)) (hamField (mass hκ n) (γ σ)) := by
        unfold omega
        rw [← inner_conj_symm, Complex.conj_im]
        ring
      linarith
    rw [h2] at h1
    exact h1
  have hc := is_const_of_deriv_eq_zero (f := fun σ => mass hκ n (γ σ))
    (fun σ => (hd σ).differentiableAt) (fun σ => (hd σ).deriv) τ 0
  exact hc

/-- Equal actions: the same full phase torus. -/
theorem on_torus (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) {u v : L2T L}
    (h : ∀ n, mass hκ n v = mass hκ n u) : ∃ ψ : Torus, v = Tact (L := L) hκ ψ u := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, -, -, hΨΦ, -, hmass, -, -, -, -, -, -, -, hrotψ, -, -, -⟩ := hG.2
  have hn : ∀ n, ‖Φ v n‖ = ‖Φ u n‖ := by
    intro n
    have h1 := hmass v n
    have h2 := hmass u n
    have h3 : (RootIndexedMasses.masses hκ v).1 n = (RootIndexedMasses.masses hκ u).1 n := h n
    rw [← h1, ← h2] at h3
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
  classical
  let χ : Torus := fun n => if Φ u n = 0 then 1 else Circle.exp (Complex.arg (Φ v n / Φ u n))
  have hχ : ∀ n, (χ n : ℂ) * Φ u n = Φ v n := by
    intro n
    by_cases h0 : Φ u n = 0
    · have hv0 : Φ v n = 0 := by rw [← norm_eq_zero, hn n, h0, norm_zero]
      simp [χ, h0, hv0]
    · simp only [χ, if_neg h0, Circle.coe_exp]
      have hnorm : ‖Φ v n / Φ u n‖ = 1 := by
        rw [norm_div, hn n, div_self (norm_ne_zero_iff.mpr h0)]
      have he := Complex.norm_mul_exp_arg_mul_I (Φ v n / Φ u n)
      rw [hnorm, Complex.ofReal_one, one_mul] at he
      rw [he]
      field_simp
  refine ⟨χ⁻¹, ?_⟩
  have hΦ : Φ (Tact (L := L) hκ χ⁻¹ u) = Φ v := by
    rw [hrotψ, inv_inv]
    refine lp.ext (funext fun n => ?_)
    rw [rotate_apply, hχ n]
  rw [← hΨΦ v, ← hΦ, hΨΦ]

/-- **Gradient agreement on the whole phase torus** (eq:MP-full-gradient-agreement), from the identity at `u`. -/
theorem grad_transport (hκ : 0 < κ) (hG : GlobalStatement L κ hκ d Φl Ψl) {F W : L2T L → ℝ}
    (hF : ∀ ψ v, F (Tact (L := L) hκ ψ v) = F v) (hW : ∀ ψ v, W (Tact (L := L) hκ ψ v) = W v)
    (hFd : Differentiable ℝ F) (u : L2T L) (hWd : DifferentiableAt ℝ W u) {nI : ℕ} (n : Fin nI → ℤ)
    (θf : Fin nI → ℝ)
    (hgrad : fderiv ℝ F u = fderiv ℝ W u + ∑ i, θf i • fderiv ℝ (mass hκ (n i)) u) (ψ : Torus) :
    DifferentiableAt ℝ W (Tact (L := L) hκ ψ u) ∧
      fderiv ℝ F (Tact (L := L) hκ ψ u) =
        fderiv ℝ W (Tact (L := L) hκ ψ u) + ∑ i, θf i • fderiv ℝ (mass hκ (n i)) (Tact (L := L) hκ ψ u) := by
  set y := Tact (L := L) hκ ψ u with hy
  -- differentiability of `W` at `y`
  obtain ⟨E', hE', -, -⟩ := Tact_deriv hκ hG ψ⁻¹ y
  have hyu : Tact (L := L) hκ ψ⁻¹ y = u := Tact_one_mul hκ hG ψ u
  have hWy : DifferentiableAt ℝ W y := by
    have hd : DifferentiableAt ℝ W (Tact (L := L) hκ ψ⁻¹ y) := by rw [hyu]; exact hWd
    have hc := hd.hasFDerivAt.comp y hE'
    have : W ∘ Tact (L := L) hκ ψ⁻¹ = W := funext (hW ψ⁻¹)
    rw [this] at hc
    exact hc.differentiableAt
  refine ⟨hWy, ?_⟩
  obtain ⟨E, hE, hs, -⟩ := Tact_deriv hκ hG ψ u
  have hFu := fderiv_inv hκ ψ (hF ψ) (hFd y) hE
  have hWu := fderiv_inv hκ ψ (hW ψ) hWy hE
  have hMu : ∀ i, HasFDerivAt (mass hκ (n i)) ((fderiv ℝ (mass hκ (n i)) y).comp E) u := fun i =>
    fderiv_inv hκ ψ (mass_Tact hκ hG ψ (n i)) (R52CFOrbit.differentiableAt_mass hκ (n i) y) hE
  ext k
  obtain ⟨k', rfl⟩ := hs k
  have h1 := congrArg (fun A : L2T L →L[ℝ] ℝ => A k') hgrad
  simp only [hFu.fderiv, hWu.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    fun i => (hMu i).fderiv] at h1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  exact h1

/-- **The field splits on the torus**: `X_F = X_W + X_{Σ θ_i I_{n_i}}` wherever the differentials agree. -/
theorem field_split {F W : L2T L → ℝ} (hκ : 0 < κ) {y : L2T L} (hWy : DifferentiableAt ℝ W y)
    {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ)
    (hgrad : fderiv ℝ F y = fderiv ℝ W y + ∑ i, θf i • fderiv ℝ (mass hκ (n i)) y) :
    hamField F y = hamField W y + hamField (fun v => ∑ i, θf i * mass hκ (n i) v) y := by
  have hM : HasFDerivAt (fun v => ∑ i, θf i * mass hκ (n i) v) (∑ i, θf i • fderiv ℝ (mass hκ (n i)) y) y :=
    HasFDerivAt.fun_sum fun i _ => (R52CFOrbit.differentiableAt_mass hκ (n i) y).hasFDerivAt.const_mul (θf i)
  have h : fderiv ℝ F y = fderiv ℝ W y + fderiv ℝ (fun v => ∑ i, θf i * mass hκ (n i) v) y := by
    rw [hM.fderiv]; exact hgrad
  exact hamField_add_of h

end QuantumNLS.Prop025OTorus

#print axioms QuantumNLS.Prop025OTorus.Tact_deriv
#print axioms QuantumNLS.Prop025OTorus.hamField_equiv
#print axioms QuantumNLS.Prop025OTorus.windowFamily_Tact
#print axioms QuantumNLS.Prop025OTorus.mass_conserved
#print axioms QuantumNLS.Prop025OTorus.on_torus
#print axioms QuantumNLS.Prop025OTorus.grad_transport
#print axioms QuantumNLS.Prop025OTorus.field_split

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OTorus." then
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
  Lean.logInfo m!"Prop025OTorus aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
