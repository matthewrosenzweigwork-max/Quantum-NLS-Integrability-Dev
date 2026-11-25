import Mathlib

/-! GP-04: differential solutions constructed from Picard fixed points,
local uniqueness, and exponential continuous dependence. Variational and
analytic initial dependence are not assumed or asserted here. -/
set_option autoImplicit false
noncomputable section
open Set Metric Topology Filter ODE
open scoped NNReal
namespace QuantumNLS.Ext025A2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard's actual fixed point is continuous, stays in the chosen ball,
satisfies the integral equation, and solves the differential equation. -/
theorem gp04_differential_existence {f : ℝ → E → E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, Continuous α ∧ α t₀ = x ∧
      (∀ t, α t ∈ closedBall x₀ a) ∧
      (∀ t ∈ Icc tmin tmax, α t = ODE.picard f t₀ x α t) ∧
      (∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) := by
  obtain ⟨β, hβ⟩ := FunSpace.exists_isFixedPt_next hf hx
  let γ := FunSpace.next hf hx β
  have heq : ∀ t ∈ Icc tmin tmax,
      γ.compProj t = ODE.picard f t₀ x γ.compProj t := by
    intro t ht
    have hg : γ = β := hβ
    rw [hg, FunSpace.compProj_of_mem ht]
    exact (FunSpace.isFixedPt_next_iff hf hx).mp hβ ⟨t, ht⟩
  have hcont := γ.continuous_compProj
  have hmem : ∀ t, γ.compProj t ∈ closedBall x₀ a :=
    fun _ => γ.compProj_mem_closedBall hf.mul_max_le
  refine ⟨γ.compProj, hcont, ?_, hmem, heq, ?_⟩
  · simp [γ]
  · intro t ht
    exact (ODE.hasDerivWithinAt_picard_Icc t₀.property hf.continuousOn_uncurry
      hcont.continuousOn (fun t _ => hmem t) x ht).congr heq (heq t ht)

omit [CompleteSpace E] in
/-- Two continuous differential solutions in the same local Lipschitz ball agree. -/
theorem gp04_uniqueness {f : ℝ → E → E} {S : ℝ → Set E} {a b t₀ : ℝ}
    {K : ℝ≥0} {α β : ℝ → E}
    (hL : ∀ t ∈ Ioo a b, LipschitzOnWith K (f t) (S t)) (ht₀ : t₀ ∈ Ioo a b)
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t ∈ Ioo a b, HasDerivAt α (f t (α t)) t)
    (hmα : ∀ t ∈ Ioo a b, α t ∈ S t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t ∈ Ioo a b, HasDerivAt β (f t (β t)) t)
    (hmβ : ∀ t ∈ Ioo a b, β t ∈ S t) (hinit : α t₀ = β t₀) :
    EqOn α β (Icc a b) :=
  ODE_solution_unique_of_mem_Icc hL ht₀ hα hdα hmα hβ hdβ hmβ hinit

omit [CompleteSpace E] in
/-- The exact exponential bound for the distance of two local trajectories. -/
theorem gp04_exponential_dependence {f : ℝ → E → E} {S : ℝ → Set E} {a b δ : ℝ}
    {K : ℝ≥0} {α β : ℝ → E}
    (hL : ∀ t ∈ Ico a b, LipschitzOnWith K (f t) (S t))
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t ∈ Ico a b, HasDerivWithinAt α (f t (α t)) (Ici t) t)
    (hmα : ∀ t ∈ Ico a b, α t ∈ S t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t ∈ Ico a b, HasDerivWithinAt β (f t (β t)) (Ici t) t)
    (hmβ : ∀ t ∈ Ico a b, β t ∈ S t) (hinit : dist (α a) (β a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (α t) (β t) ≤ δ * Real.exp (K * (t - a)) :=
  dist_le_of_trajectories_ODE_of_mem hL hα hdα hmα hβ hdβ hmβ hinit

omit [CompleteSpace E] in
/-- Exponential norm control, including operator-valued variational solutions
when those solutions have been independently constructed. -/
theorem gp04_exponential_norm {α dα : ℝ → E} {a b C δ : ℝ}
    (hα : ContinuousOn α (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt α (dα t) (Ici t) t)
    (hinit : ‖α a‖ ≤ δ) (hbound : ∀ t ∈ Ico a b, ‖dα t‖ ≤ C * ‖α t‖) :
    ∀ t ∈ Icc a b, ‖α t‖ ≤ δ * Real.exp (C * (t - a)) := by
  simpa only [gronwallBound_ε0] using
    norm_le_gronwallBound_of_norm_deriv_right_le hα hd hinit
      (fun t ht => (hbound t ht).trans_eq (add_zero _).symm)
end QuantumNLS.Ext025A2
#print axioms QuantumNLS.Ext025A2.gp04_differential_existence
#print axioms QuantumNLS.Ext025A2.gp04_uniqueness
#print axioms QuantumNLS.Ext025A2.gp04_exponential_dependence
#print axioms QuantumNLS.Ext025A2.gp04_exponential_norm
