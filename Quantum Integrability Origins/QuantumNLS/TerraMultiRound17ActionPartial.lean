import QuantumNLS.TerraMultiRound15D01Partial

/-! Action evolution along an arbitrary actual local solution. This does not
assert existence of a global flow or its analytic dependence. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Filter Topology
open QuantumNLS.D01LocalPrimitive QuantumNLS.RealAnalyticDef
namespace QuantumNLS.TerraMultiRound17ActionPartial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every solution through time zero has exponentially scaled actions on its
interval of existence. -/
theorem action_on_solution (S : Hyp H) {a b : ℝ} (hzero : (0 : ℝ) ∈ Ioo a b)
    (u : ℝ → H) (hu : ∀ t ∈ Ioo a b, HasDerivAt u (S.Y (u t)) t) :
    ∀ t ∈ Ioo a b, ∀ n : ℤ, S.act (u t) n = Real.exp t * S.act (u 0) n := by
  intro t ht n
  let f : H → ℝ := fun x => S.act x n
  have hf : ∀ x, DifferentiableAt ℝ f x := by
    intro x
    exact (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 n).differentiableAt.comp x
      (analyticAt_of_isRealAnalyticPoly (S.act_analytic x)).differentiableAt
  have hder : ∀ s ∈ Ioo a b, HasDerivAt (fun r => f (u r)) (f (u s)) s := by
    intro s hs
    have h := (hf (u s)).hasFDerivAt.comp_hasDerivAt s (hu s hs)
    rw [(QuantumNLS.TerraMultiRound15D01Partial.action_derivative_and_self_contraction S).1 (u s) n] at h
    exact h
  have huniq := ODE_solution_unique_of_mem_Ioo (v := fun _ : ℝ => id)
    (s := fun _ => Set.univ) (K := 1) (f := fun s => f (u s))
    (g := fun s => Real.exp s * f (u 0)) (t₀ := 0)
    (fun _ _ => LipschitzWith.id.lipschitzOnWith) hzero
    (fun s hs => ⟨hder s hs, trivial⟩)
    (fun s _ => ⟨(Real.hasDerivAt_exp s).mul_const (f (u 0)), trivial⟩)
    (by simp)
  exact huniq ht

#print axioms action_on_solution
end QuantumNLS.TerraMultiRound17ActionPartial
