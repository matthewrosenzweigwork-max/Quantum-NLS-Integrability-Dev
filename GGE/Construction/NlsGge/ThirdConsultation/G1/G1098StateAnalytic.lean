import NlsGge.GK38.PairAnalytic
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.GradEigenDefs

/-! # H181 supporting module (a): analyticity of `φ ↦ state φ (muSeq φ n) a` into PairKernelCont38.
`state φ z a` is the column combination `t ↦ a 0 • fundColumn38 φ z t 0 + a 1 • fundColumn38 φ z t 1`
of the fundamental solution `fundContP φ z` (GK38/PairAnalytic.lean, jointly analytic on PotPair × ℂ).
We factor it as `psiBL38 a (fundContP φ z)`, where `psiBL38 : PairVec38 →L[ℂ] PairCont38 →L[ℂ]
PairKernelCont38` is bounded bilinear (bound `2 * ‖a‖ * ‖M‖`). Analyticity then follows from the
generic bilinear composition lemma `psi_comp_analyticAt`, the analyticity of `fundContP` on univ,
and the analyticity of `muSeq` on gkW (AngleDirichletAnalytic). No hypothesis is added. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.Pilot
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem continuous_col38 (M : PairCont38) (j : Fin 2) :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 => fun i : Fin 2 => M t i j) :=
  continuous_pi fun i => (continuous_apply j).comp ((continuous_apply i).comp M.continuous)

/-- Column combination of a continuous matrix kernel: `t ↦ Σ_j a_j • column_j (M t)`. -/
def psiFun38 (a : PairVec38) (M : PairCont38) : PairKernelCont38 :=
  ⟨fun t => a 0 • (fun i => M t i 0) + a 1 • (fun i => M t i 1),
    ((continuous_col38 M 0).const_smul (a 0)).add ((continuous_col38 M 1).const_smul (a 1))⟩

theorem psiFun38_apply (a : PairVec38) (M : PairCont38) (t : Set.Icc (0 : ℝ) 1) :
    psiFun38 a M t = a 0 • (fun i => M t i 0) + a 1 • (fun i => M t i 1) := rfl

theorem psiFun38_add_left (a a' : PairVec38) (M : PairCont38) :
    psiFun38 (a + a') M = psiFun38 a M + psiFun38 a' M := by
  ext t i
  simp only [psiFun38_apply, ContinuousMap.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem psiFun38_smul_left (c : ℂ) (a : PairVec38) (M : PairCont38) :
    psiFun38 (c • a) M = c • psiFun38 a M := by
  ext t i
  simp only [psiFun38_apply, ContinuousMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.smul_apply]
  ring

theorem psiFun38_add_right (a : PairVec38) (M M' : PairCont38) :
    psiFun38 a (M + M') = psiFun38 a M + psiFun38 a M' := by
  ext t i
  simp only [psiFun38_apply, ContinuousMap.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem psiFun38_smul_right (c : ℂ) (a : PairVec38) (M : PairCont38) :
    psiFun38 a (c • M) = c • psiFun38 a M := by
  ext t i
  simp only [psiFun38_apply, ContinuousMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_col38_le (M : PairCont38) (t : Set.Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖(fun i => M t i j : PairVec38)‖ ≤ ‖M‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact (norm_le_pi_norm (M t i) j).trans ((norm_le_pi_norm (M t) i).trans (M.norm_coe_le_norm t))

theorem norm_psiFun38_le (a : PairVec38) (M : PairCont38) :
    ‖psiFun38 a M‖ ≤ 2 * ‖a‖ * ‖M‖ := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg zero_le_two (norm_nonneg _))
    (norm_nonneg _))).2 fun t => ?_
  have h0 : ‖a 0 • (fun i => M t i 0 : PairVec38)‖ ≤ ‖a‖ * ‖M‖ := by
    rw [norm_smul]
    exact mul_le_mul (norm_le_pi_norm a 0) (norm_col38_le M t 0) (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖a 1 • (fun i => M t i 1 : PairVec38)‖ ≤ ‖a‖ * ‖M‖ := by
    rw [norm_smul]
    exact mul_le_mul (norm_le_pi_norm a 1) (norm_col38_le M t 1) (norm_nonneg _) (norm_nonneg _)
  show ‖a 0 • (fun i => M t i 0 : PairVec38) + a 1 • (fun i => M t i 1 : PairVec38)‖ ≤
    2 * ‖a‖ * ‖M‖
  have := norm_add_le (a 0 • (fun i => M t i 0 : PairVec38)) (a 1 • (fun i => M t i 1 : PairVec38))
  linarith

/-- `psiFun38` as a ℂ-bilinear map (algebraic form). -/
def psiLM38 : PairVec38 →ₗ[ℂ] PairCont38 →ₗ[ℂ] PairKernelCont38 :=
  LinearMap.mk₂ ℂ psiFun38 psiFun38_add_left psiFun38_smul_left psiFun38_add_right
    psiFun38_smul_right

/-- `psiFun38` as a bounded ℂ-bilinear map from the coefficient vectors and matrix kernels. -/
def psiBL38 : PairVec38 →L[ℂ] PairCont38 →L[ℂ] PairKernelCont38 :=
  LinearMap.mkContinuous₂ psiLM38 2 (fun a M => norm_psiFun38_le a M)

@[simp] theorem psiBL38_apply (a : PairVec38) (M : PairCont38) :
    psiBL38 a M = psiFun38 a M := rfl

/-- The state is the bilinear image of the fundamental solution. -/
theorem state_eq_psiBL38 (φ : PotPair) (z : ℂ) (a : PairVec38) :
    state φ z a = psiBL38 a (fundContP φ z) := by
  ext t i
  have hext : ext38 (fundContP φ z) (t : ℝ) = fundContP φ z t := ext38_of_mem _ t.2
  simp only [state, ContinuousMap.coe_mk, psiBL38_apply, psiFun38_apply, fundColumn38, hext,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Generic bilinear composition of analytic maps (abstract normed spaces). -/
theorem psi_comp_analyticAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G) {f : X → E} {g : X → F} {x : X}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun y => B (f y) (g y)) x :=
  AnalyticAt.comp₂ (h := fun q : E × F => B q.1 q.2) (f := f) (g := g)
    (B.analyticAt_bilinear (f x, g x)) hf hg

/-- The fundamental solution along `z(φ)` is analytic where `z` is. -/
theorem analyticAt_fundContP_along {U : Set PotPair} {z : PotPair → ℂ}
    (hz : AnalyticOnNhd ℂ z U) {φ : PotPair} (hφ : φ ∈ U) :
    AnalyticAt ℂ (fun ψ => fundContP ψ (z ψ)) φ :=
  AnalyticAt.comp (g := fun p : PotPair × ℂ => fundContP p.1 p.2) (f := fun ψ => (ψ, z ψ))
    (analyticOnNhd_fundContP (φ, z φ) (Set.mem_univ _))
    (analyticAt_id.prod (hz φ hφ))

/-- Analyticity of the terminal seed along `z(φ)`, as a `PairVec38`-valued map. -/
theorem analyticAt_terminalSeed_along {U : Set PotPair} {z : PotPair → ℂ}
    (hz : AnalyticOnNhd ℂ z U) {φ : PotPair} (hφ : φ ∈ U) :
    AnalyticAt ℂ (fun ψ => terminalSeed ψ (z ψ)) φ := by
  have hm : ∀ i j : Fin 2, AnalyticAt ℂ (fun ψ => monodromyPair ψ (z ψ) i j) φ := fun i j =>
    AnalyticAt.comp (g := fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j)
      (f := fun ψ => (ψ, z ψ)) (analyticOnNhd_monodromyPair i j (φ, z φ) (Set.mem_univ _))
      (analyticAt_id.prod (hz φ hφ))
  refine analyticAt_pi_iff.2 fun i => ?_
  fin_cases i
  · exact (hm 0 1).add (hm 1 1)
  · exact (hm 0 0).add (hm 1 0) |>.neg

/-- Analyticity of `φ ↦ state φ (z φ) a` on the set where `z` is analytic (constant `a`). -/
theorem analyticOnNhd_state_along (U : Set PotPair) (z : PotPair → ℂ)
    (hz : AnalyticOnNhd ℂ z U) (a : PairVec38) :
    AnalyticOnNhd ℂ (fun φ => state φ (z φ) a) U := by
  intro φ hφ
  have heq : (fun ψ => state ψ (z ψ) a) = fun ψ => psiBL38 a (fundContP ψ (z ψ)) :=
    funext fun ψ => state_eq_psiBL38 ψ (z ψ) a
  rw [heq]
  exact ((psiBL38 a).analyticAt _).comp (analyticAt_fundContP_along hz hφ)

/-- Analyticity of `φ ↦ state φ (z φ) (terminalSeed φ (z φ))` on the set where `z` is analytic. -/
theorem analyticOnNhd_state_terminal_along (U : Set PotPair) (z : PotPair → ℂ)
    (hz : AnalyticOnNhd ℂ z U) :
    AnalyticOnNhd ℂ (fun φ => state φ (z φ) (terminalSeed φ (z φ))) U := by
  intro φ hφ
  have heq : (fun ψ => state ψ (z ψ) (terminalSeed ψ (z ψ))) =
      fun ψ => psiBL38 (terminalSeed ψ (z ψ)) (fundContP ψ (z ψ)) :=
    funext fun ψ => state_eq_psiBL38 ψ (z ψ) (terminalSeed ψ (z ψ))
  rw [heq]
  exact psi_comp_analyticAt psiBL38 (analyticAt_terminalSeed_along hz hφ)
    (analyticAt_fundContP_along hz hφ)

/-- F-state analyticity at `muSeq`: the first state of the mixed kernel, on gkW. -/
theorem analyticOnNhd_state_muSeq_const (n : ℤ) (a : PairVec38) :
    AnalyticOnNhd ℂ (fun φ => state φ (muSeq φ n) a) gkW :=
  analyticOnNhd_state_along gkW (fun φ => muSeq φ n) (analyticOnNhd_muSeq_complex38 n) a

/-- The complex terminal state `complexTerminalState`-shape, analytic on gkW. -/
theorem analyticOnNhd_state_muSeq_terminal (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => state φ (muSeq φ n) (terminalSeed φ (muSeq φ n))) gkW :=
  analyticOnNhd_state_terminal_along gkW (fun φ => muSeq φ n) (analyticOnNhd_muSeq_complex38 n)

end
end NlsGge.GK38.GradEigen38
