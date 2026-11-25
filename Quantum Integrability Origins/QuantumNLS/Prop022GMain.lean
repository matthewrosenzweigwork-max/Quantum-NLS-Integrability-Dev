import Mathlib
import QuantumNLS.Prop022GHilbert
import QuantumNLS.Prop022GLinear

/-! PROP-022 general-scope transport, stage G3d: printed conclusions 1-3 of Q7B:lem:pair
(fluctuations.tex:93-104) on an arbitrary complex separable infinite-dimensional Hilbert space.

Scope (for the reviewer):
* Covered: the classical side only, i.e. (1) the pair kernel is Hilbert--Schmidt and both
  coefficient bounds eq:pair; (2) `S = α + β̄`-decomposition and the linearized equation;
  (3) the β estimate eq:beta.  The Fock-side conclusions (quadratic propagator, implementation,
  pure quasifree vacuum, number identity) are NOT stated here: the definition of the Weyl
  operator / `Q(t)` / quasifree predicate over a general `H` awaits the owner's A/B/C decision.
* Every object is either defined on `H` without a unitary (`symbolH`, the HS sum `antiHS` over an
  arbitrary Hilbert basis `e`) or defined through a unitary `U : H ≃ₗᵢ[ℂ] L2T L` and proved to be
  independent of `U` (gradient, trajectory, `S`, `a_t`, `b_t`, `α`, `β`), and characterized
  intrinsically (gradient by `dF = 2 Re⟪∇F, ·⟫`; trajectory and `S` as unique solutions).
* `a_t`, `b_t` are the complex-linear and antilinear parts of the Hessian `D(∇F)(u_t)` (the printed
  "interpreted intrinsically ... as an antilinear operator"); `α`, `β` are `(S ∓ iSi)/2`.
* Rank-zero kernel set to zero, `C_A = pairMajorant A`, as in the accepted torus instance. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022GMain
open PhysicalTensor Prop022GAntiHS Prop022GClassical Prop022GLinear Prop022FactorialMajorantR115

/-- **PROP-022 (Q7B:lem:pair), printed conclusions 1-3 on a general complex separable
infinite-dimensional Hilbert space `H`.** -/
theorem PROP022_general_classical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H)
    (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] L2T L) ∧
    ∀ U : H ≃ₗᵢ[ℂ] L2T L,
    let F := symbolH K
    let grad := gradH U K
    let Φ := flowH U K M A hA.le hK hs
    let u := profH U K M A hA.le hK hs u₀ hu₀
    let S := SH U K M A hA.le hK hs u₀ hu₀
    let a := aH U K M A hA.le hK hs u₀ hu₀
    let b := bH U K M A hA.le hK hs u₀ hu₀
    let α := alphaH U K M A hA.le hK hs u₀ hu₀
    let β := betaH U K M A hA.le hK hs u₀ hu₀
    -- the classical data: F intrinsic on H, its gradient, F = F_L ∘ U
    (∀ v, HasFDerivAt F (realDual (grad v)) v) ∧
    (∀ v, F v = Prop022ClassicalTimeR116.classicalSeries (BL U K) (U v)) ∧
    -- the flow -i∇F, the trajectory (unique among unit solutions), S = DΦ_{t-s}(u_s)
    (∀ x, Φ 0 x = x ∧ ∀ t, HasDerivAt (fun r => Φ r x) ((-Complex.I) • grad (Φ t x)) t ∧
      ‖Φ t x‖ = ‖x‖) ∧
    (u 0 = u₀ ∧ ∀ t, ‖u t‖ = 1 ∧ HasDerivAt u ((-Complex.I) • grad (u t)) t) ∧
    (∀ γ : ℝ → H, γ 0 = u₀ → (∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • grad (γ t)) t) →
      γ = u) ∧
    (∀ s t, Φ (t - s) (u s) = u t) ∧
    (∀ t s, S t s = fderiv ℝ (Φ (t - s)) (u s)) ∧
    -- (1) b_t Hilbert--Schmidt (in the arbitrary basis e) and both printed bounds
    (∀ t, CLinear (a t) ∧ (∀ x y, ⟪x, a t y⟫_ℂ = ⟪a t x, y⟫_ℂ) ∧
      Antilinear (b t) ∧ (∀ x y, ⟪x, b t y⟫_ℂ = ⟪y, b t x⟫_ℂ) ∧
      antiHS e (b t) ≠ ⊤ ∧ Real.sqrt ((antiHS e (b t)).toReal) ≤ pairMajorant A * M ∧
      ‖a t‖ ≤ M * ∑' r : ℕ, (((r+1 : ℕ) : ℝ)^2 * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
    -- (2) the linearized equation and S = α + β with α complex-linear, β antilinear
    (∀ s t x, Complex.I • deriv (fun r => S r s x) t = a t (S t s x) + b t (S t s x)) ∧
    (∀ t s, S t s = α t s + β t s ∧ CLinear (α t s) ∧ Antilinear (β t s)) ∧
    -- (3) the β estimate under the printed P hypothesis, including negative time
    ((∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) → ∀ t, |t| ≤ T →
      antiHS e (β t 0) ≠ ⊤ ∧ Real.sqrt ((antiHS e (β t 0)).toReal) ≤ |t| * pairMajorant A * M * P) ∧
    -- independence of the transporting unitary
    (∀ U' : H ≃ₗᵢ[ℂ] L2T L, gradH U' K = grad ∧ profH U' K M A hA.le hK hs u₀ hu₀ = u ∧
      SH U' K M A hA.le hK hs u₀ hu₀ = S ∧ aH U' K M A hA.le hK hs u₀ hu₀ = a ∧
      bH U' K M A hA.le hK hs u₀ hu₀ = b ∧ alphaH U' K M A hA.le hK hs u₀ hu₀ = α ∧
      betaH U' K M A hA.le hK hs u₀ hu₀ = β) := by
  refine ⟨Prop022GHilbert.exists_unitary_L2T L hH, fun U => ?_⟩
  intro F grad Φ u S a b α β
  refine ⟨fun v => symbolH_hasFDerivAt U K M A hA.le hK hs v, fun v => symbolH_eq U K v,
    fun x => flowH_spec U K M A hA.le hK hs x, profH_spec U K M A hA.le hK hs u₀ hu₀,
    fun γ h0 hγ => profH_unique U K M A hA.le hK hs u₀ hu₀ γ h0 hγ,
    fun s t => flowH_profH U K M A hA.le hK hs u₀ hu₀ s t, fun t s => rfl, fun t => ?_,
    fun s t x => linearized U K M A hA.le hK hs u₀ hu₀ s t x,
    fun t s => ?_, fun hS t ht => beta_estimate U K M A hA.le hK hs u₀ hu₀ hM e T P hP hS t ht,
    fun U' => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := bH_bounds U K M A hA.le hK hs u₀ hu₀ e t
    exact ⟨aH_clinear U K M A hA.le hK hs u₀ hu₀ t, aH_hermitian U K M A hA.le hK hs u₀ hu₀ t,
      bH_antilinear U K M A hA.le hK hs u₀ hu₀ t, bH_symmetric U K M A hA.le hK hs u₀ hu₀ t,
      h1, h2, h3⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := SH_blocks U K M A hA.le hK hs u₀ hu₀ t s
    exact ⟨h1, h2, h3⟩
  · refine ⟨funext (fun v => gradH_indep U' U K M A hA.le hK hs v),
      profH_indep U' U K M A hA.le hK hs u₀ hu₀,
      funext (fun t => funext (fun s => SH_indep U' U K M A hA.le hK hs u₀ hu₀ t s)),
      funext (fun t => aH_indep U' U K M A hA.le hK hs u₀ hu₀ t),
      funext (fun t => bH_indep U' U K M A hA.le hK hs u₀ hu₀ t),
      funext (fun t => funext (fun s => alphaH_indep U' U K M A hA.le hK hs u₀ hu₀ t s)),
      funext (fun t => funext (fun s => betaH_indep U' U K M A hA.le hK hs u₀ hu₀ t s))⟩

/-- Basis independence of the HS norms in the theorem (any two Hilbert bases of `H`). -/
theorem hs_basis_independent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℝ] H} (hT : Antilinear T) {ι κ : Type*}
    (e : HilbertBasis ι ℂ H) (e' : HilbertBasis κ ℂ H) : antiHS e T = antiHS e' T :=
  antiHS_basis_indep hT e e'

end QuantumNLS.Prop022GMain

#print axioms QuantumNLS.Prop022GMain.PROP022_general_classical
#print axioms QuantumNLS.Prop022GMain.hs_basis_independent

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    for p in ["QuantumNLS.Prop022GTensor.", "QuantumNLS.Prop022GHilbert.", "QuantumNLS.Prop022GAntiHS.",
        "QuantumNLS.Prop022GClassical.", "QuantumNLS.Prop022GLinear.", "QuantumNLS.Prop022GMain."] do
      if n.toString.startsWith p then
        pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Prop022G aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
