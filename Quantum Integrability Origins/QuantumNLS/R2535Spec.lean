import QuantumNLS.RealAnalyticDef

/-! integrator-authored trusted spec for R-2535E8FD `global:analytic-identity`
(global/individual_periods.tex:115). E, F real Hilbert spaces; A : E → F locally real analytic
everywhere in the sense of DEF-017's first clause (near each input, a series of continuous real
homogeneous polynomials converging in norm), written out here independently; if A vanishes on an open
ball about zero (positive radius), then A vanishes on all of E. -/

open Filter Topology Finset

namespace QuantumNLS.R2535Spec

/-- DEF-017 first clause, written independently: continuous real homogeneous polynomials P n of degree
n (P n h = M(h,…,h) for a real n-linear M, P n continuous) and r > 0 with Σ P n (y − x) → f y in norm
for ‖y − x‖ < r. -/
def LocRealAnalytic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : Prop :=
  ∃ P : ℕ → E → F,
    (∀ n, Continuous (P n) ∧ ∃ M : MultilinearMap ℝ (fun _ : Fin n => E) F, ∀ h, P n h = M (fun _ => h)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ y, ‖y - x‖ < r →
      Tendsto (fun N => ∑ n ∈ range N, P n (y - x)) atTop (𝓝 (f y))

def Spec : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (A : E → F),
    (∀ x, LocRealAnalytic A x) → ∀ ρ : ℝ, 0 < ρ →
    (∀ y ∈ Metric.ball (0 : E) ρ, A y = 0) → ∀ x : E, A x = 0

theorem spec : Spec := by
  intro E F _ _ _ _ _ _ A hA ρ hρ hz
  exact QuantumNLS.RealAnalyticDef.identity_of_vanishing_ball_poly A (fun x => hA x) hρ hz

end QuantumNLS.R2535Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R2535Spec.spec
  IO.println s!"R2535Spec.spec axioms: {ax}"
