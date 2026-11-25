import QuantumNLS.Bind7BDEF024H01
/-! integrator-authored trusted spec for DEF-024 all orders (hierarchy-bound; READY r99; NOT promoted: owner hold): headline statement(s) copied verbatim from Bind7BDEF024H01 (QuantumNLS.Bind7BDEF024H01). -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.D24FullSpec
open QuantumNLS.Bind7BDEF024H01
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem DEF024_bound_spec (hκ : 0 < κ) :
    -- (a) existence, uniqueness and commutation of the higher classical flows, every finite 𝓡
    (∀ 𝓡 : Finset ℕ, QuantumNLS.RB7.Clause1 L κ 𝓡 ∧ QuantumNLS.RB7.Clause2 L κ 𝓡) ∧
    -- (b) finite loss, at every order
    (∃ C : QuantumNLS.RB7.ChartFacts (L := L) hκ, ∀ (r m : ℕ) (q : NNReal),
      QuantumNLS.Def024LossR32m.OrderFiniteLoss
        (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ) C r m q) ∧
    -- (c) joint classical flow: composition of Hamiltonian flows, jointly C^∞ in all times and space
    (∀ 𝓡 : Finset ℕ,
      (∃ F : QuantumNLS.HierarchyFlow.HamFlows L κ 𝓡, ∀ u : ℝ → ℂ,
          QuantumNLS.ClassicalCharges.SmoothPeriodic L u → QuantumNLS.Def024LossR32m.JointContDiff F u) ∧
      ∀ (F : QuantumNLS.HierarchyFlow.HamFlows L κ 𝓡) (u : ℝ → ℂ),
          QuantumNLS.ClassicalCharges.SmoothPeriodic L u → QuantumNLS.Def024LossR32m.JointContDiff F u) ∧
    -- (d) the fixed compact box of joint times
    (∀ D : QuantumNLS.HierarchyFlow.TestData L, IsCompact D.box) ∧
    -- (e) the quantum flow U_N(t) = exp(-i Σ_{r∈𝓡} t_r Q_{N,r}) in a Bethe basis
    (∀ (N : ℕ) (b : QuantumNLS.BetheCoefficientTransform.BetheBasis L N) (c : ℝ) (𝓡 : Finset ℕ)
      (t : ℕ → ℝ) (ψ : QuantumNLS.BetheCoefficientTransform.HN L N)
      (m : QuantumNLS.BetheLabels.MArr N),
      ⟪b m, QuantumNLS.HierarchyFlow.quantumFlow b c 𝓡 t ψ⟫_ℂ =
        Complex.exp (-((∑ r ∈ 𝓡, t r * QuantumNLS.BetheSpectralCharges.eigenvalue L N (c / N) r m : ℝ) : ℂ)
          * Complex.I) * ⟪b m, ψ⟫_ℂ) := by
  first
  | exact QuantumNLS.Bind7BDEF024H01.DEF024_bound
  | (apply QuantumNLS.Bind7BDEF024H01.DEF024_bound <;> assumption)

end QuantumNLS.D24FullSpec
#print axioms QuantumNLS.D24FullSpec.DEF024_bound_spec
