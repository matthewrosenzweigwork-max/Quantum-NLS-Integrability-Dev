import QuantumNLS.Ext025A4D01Analytic
import QuantumNLS.TerraMultiRound19D01Full
import QuantumNLS.D01Reconstruction

/-! Exact D01 source consumer instantiation. Both printed source statements
are retained, with their formerly open GP04CompactLocalAnalyticity premise
discharged by the constructed theorem. Earlier sources remain read-only. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Ext025A4D01Discharge
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.StrongSymplectic
open QuantumNLS.TerraMultiRound18Flow QuantumNLS.TerraMultiRound18AnalyticFlow
open QuantumNLS.D01Reconstruction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem global_D01_completeness (S : Hyp H) :
    ∃ F : ℝ → H → H,
      (∀ u, F 0 u = u) ∧
      (∀ u t, HasDerivAt (fun s => F s u) (S.Y (F t u)) t) ∧
      (∀ u (γ : ℝ → H), γ 0 = u →
        (∀ t, HasDerivAt γ (S.Y (γ t)) t) → ∀ t, F t u = γ t) ∧
      (∀ t s u, F (t + s) u = F t (F s u)) ∧
      (∀ t u, F (-t) (F t u) = u ∧ F t (F (-t) u) = u) ∧
      (∀ t u, AnalyticAt ℝ (F t) u) ∧
      (∀ t u, S.act (F t u) = Real.exp t • S.act u) ∧
      (∀ t u, ‖F t u‖ = Real.exp (t / 2) * ‖u‖) ∧
      (∀ t u h k, omega (fderiv ℝ (F t) u h) (fderiv ℝ (F t) u k) =
        Real.exp t * omega h k) ∧
      (∀ t u h, S.abar (F t u) (fderiv ℝ (F t) u h) =
        Real.exp t * S.abar u h) :=
  QuantumNLS.TerraMultiRound19D01Full.global_D01_completeness S (QuantumNLS.Ext025A4D01Analytic.compact_local_analyticity S)

theorem global_D01_reconstruction (S : Hyp H) :
    -- the complete real-analytic flow of `Y = W⁻¹ ᾱ` and `(eq:global-D01-flow-identities)`
    ((∀ u, flow S 0 u = u) ∧
      (∀ u t, HasDerivAt (fun s => flow S s u) (S.Y (flow S t u)) t) ∧
      (∀ t u, AnalyticAt ℝ (flow S t) u) ∧
      (∀ t u, S.act (flow S t u) = Real.exp t • S.act u) ∧
      (∀ t u, ‖flow S t u‖ = Real.exp (t / 2) * ‖u‖) ∧
      (∀ t u h k, omega (fderiv ℝ (flow S t) u h) (fderiv ℝ (flow S t) u k) =
        Real.exp t * omega h k) ∧
      (∀ t u h, S.abar (flow S t u) (fderiv ℝ (flow S t) u h) = Real.exp t * S.abar u h)) ∧
    -- `Φ`: real analytic, strong symplectic, `(eq:global-D01-forward)` independent of `t`, extends `φ`
    ((∀ u, AnalyticAt ℝ (Phi S) u) ∧ IsStronglySymplectic (Phi S) ∧
      (∀ (u : H) (t : ℝ), 0 ≤ t → Real.exp (-t / 2) * ‖u‖ < S.ε →
        Phi S u = Real.exp (t / 2) • S.phi (flow S (-t) u)) ∧
      (∀ u ∈ S.B, Phi S u = S.phi u)) ∧
    -- `Ψ`: real analytic inverse, `(eq:global-D01-inverse)` independent of `t`
    ((∀ z, AnalyticAt ℝ (Psi S) z) ∧
      (∀ (z : K) (t : ℝ), 0 ≤ t → Real.exp (-t / 2) * ‖z‖ < S.ε →
        Psi S z = flow S t (S.psi (Real.exp (-t / 2) • z))) ∧
      (∀ u, Psi S (Phi S u) = u) ∧ (∀ z, Phi S (Psi S z) = z)) ∧
    -- `(eq:global-D01-global-identities)`
    ((∀ u n, q n (Phi S u) = S.act u n) ∧ (∀ u, ‖Phi S u‖ = ‖u‖) ∧
      (∀ u h k, omega (fderiv ℝ (Phi S) u h) (fderiv ℝ (Phi S) u k) = omega h k) ∧
      (∀ u h, alphaF (Phi S u) (fderiv ℝ (Phi S) u h) = S.abar u h)) ∧
    -- `I(H) = ℓ¹_+`
    (∀ a : L1, (∀ n, 0 ≤ a n) → ∃ u : H, S.act u = a) ∧
    -- `DΦ(u)` is a bounded real-linear isomorphism with bounded inverse `DΨ(Φ(u))`
    (∀ u : H, (fderiv ℝ (Psi S) (Phi S u)).comp (fderiv ℝ (Phi S) u) = ContinuousLinearMap.id ℝ H ∧
      (fderiv ℝ (Phi S) u).comp (fderiv ℝ (Psi S) (Phi S u)) = ContinuousLinearMap.id ℝ K) :=
  QuantumNLS.D01Reconstruction.global_D01_reconstruction S (QuantumNLS.Ext025A4D01Analytic.compact_local_analyticity S)

theorem analytic_initial_dependence (S : Hyp H) (t : ℝ) (u : H) :
    AnalyticAt ℝ (flow S t) u :=
  QuantumNLS.TerraMultiRound18AnalyticFlow.analytic_initial_dependence S
    (QuantumNLS.Ext025A4D01Analytic.compact_local_analyticity S) t u

end QuantumNLS.Ext025A4D01Discharge

#print axioms QuantumNLS.Ext025A4D01Discharge.global_D01_completeness
#print axioms QuantumNLS.Ext025A4D01Discharge.global_D01_reconstruction
#print axioms QuantumNLS.Ext025A4D01Discharge.analytic_initial_dependence

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4D01Discharge" then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
