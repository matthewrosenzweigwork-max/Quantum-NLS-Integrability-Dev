import QuantumNLS.D01ReconAnalytic

/-!
# `thm:global-D01-reconstruction` (R-701613DA) as one named theorem

Source: `source-text/chapters/global/liouville_reconstruction.tex`, Theorem `thm:global-D01-reconstruction` (line 59) with its proof (lines 296-382).

Hypotheses: `S : Hyp H` bundles items 1-4 of the printed theorem literally (`D01LocalPrimitive.Hyp`, R-81E9AAB6, accepted).
Carried open premise, as an explicit named hypothesis: `ha : GP04CompactLocalAnalyticity S`
(terra_multi's `TerraMultiRound18AnalyticFlow.GP04CompactLocalAnalyticity`; the GP-04 analytic-initial-dependence remainder that Sol r92 is proving). It is exactly the open premise of R-B390B5E9
(`lem:global-D01-completeness`) in terra_multi's frozen `TerraMultiRound19D01Full.global_D01_completeness`, whose flow (`TerraMultiRound18Flow.flow`) is used here read-only; the flow's existence, uniqueness, group law and the
action and mass identities are unconditional (Round 18) and are not assumed.

Conclusions, in the order of the printed statement: the complete flow `F_t` of `Y = W⁻¹ᾱ` (`flow S t`) with `(eq:global-D01-flow-identities)`; the real-analytic strong symplectic diffeomorphism `Φ : H → K` extending `φ` with the formula `(eq:global-D01-forward)` independent of the admissible `t`;
its real-analytic inverse `Ψ` with `(eq:global-D01-inverse)` independent of `t`; the global identities `(eq:global-D01-global-identities)`; `I(H) = ℓ¹_+`; and the bounded inverse differential `DΨ(Φ(u))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology
open Filter Set

namespace QuantumNLS.D01Reconstruction

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.StrongSymplectic
open QuantumNLS.TerraMultiRound18Flow QuantumNLS.TerraMultiRound18AnalyticFlow
open QuantumNLS.TerraMultiRound18Pullbacks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`thm:global-D01-reconstruction`** (R-701613DA). -/
theorem global_D01_reconstruction (S : Hyp H) (ha : GP04CompactLocalAnalyticity S) :
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
  ⟨⟨fun u => (flow_spec S u).1, fun u t => (flow_spec S u).2 t,
      fun t u => analytic_initial_dependence S ha t u,
      fun t u => (flow_action_mass S t u).1, fun t u => norm_flow S t u,
      conformal_symplectic S ha, one_form_pullback S ha⟩,
    ⟨fun u => Phi_analyticAt ha u, Phi_stronglySymplectic ha,
      fun u t ht h => (Phi_eq S ⟨ht, h⟩), fun u hu => Phi_ball S hu⟩,
    ⟨fun z => Psi_analyticAt ha z, fun z t ht h => Psi_eq S ⟨ht, h⟩, Psi_Phi S, Phi_Psi S⟩,
    ⟨q_Phi S, norm_Phi S, Phi_symp ha, Phi_alpha ha⟩,
    fun a ha' => act_surj S a ha',
    fun u => ⟨dPsi_dPhi ha u, dPhi_dPsi ha u⟩⟩

#print axioms global_D01_reconstruction

end QuantumNLS.D01Reconstruction
