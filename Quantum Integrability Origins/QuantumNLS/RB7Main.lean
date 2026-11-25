import Mathlib
import QuantumNLS.RB7Scale

/-!
# R-7B122087 `thm:hierarchy`: the sequence-side statement (INTERMEDIATE theorem, explicit hypotheses)

`seq_hierarchy` collects, for a family `SeqData` of `C²` rotation-invariant functionals `F_r` on weighted sequence spaces (printed:
`F_r = I_{r+1} ∘ (Z^new)^{-1}` on `h^{s_r}`), everything the printed proof derives in coordinates, without any chart:

1. `∇_j F_r(z) = Ω_{r,j}(z) z_j` with real `Ω_{r,j}`, constant on modulus tori; `|Ω_{r,j}(z)| ≤ C_z (W_r)_j`;
2. the flows `z_j(t) = e^{-i Σ_r t_r Ω_{r,j}(z)} z_j`: `flow 0 = id`, group law, commutation of every finite family;
3. constant moduli and conservation of every `F_r`;
4. full orbits are relatively compact (closure of the orbit is compact) and `(t,z) ↦ flow t z` is jointly continuous;
5. for data with finite `P`-moments every single-parameter flow is `C^∞` in `t` into `WSeq V` and solves `ż_j = -i Σ_r s_r ∇_j F_r`.

The final theorem will feed this with `F_r = I_{r+1} ∘ (Z^new)^{-1}` (chart R-F5355ABD, `lem:loss` R-8C922B25, REG-015 homeomorphisms,
R-275B7656/R-063C168E invariance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

theorem seq_hierarchy {V : PosWeight} {ι : Type} [Fintype ι] (S : SeqData V ι) :
    (∀ (r : ι) (z : WSeq V) (j : ℤ),
      grad (fderiv ℝ (S.F r) (S.down r z)) j = (S.D.Ω r z j : ℂ) * z.val j) ∧
    (∀ (r : ι) (u : ℤ → Circle) (z : WSeq V) (j : ℤ), S.D.Ω r (rot u z) j = S.D.Ω r z j) ∧
    (∀ z : WSeq V, ∃ K : ℝ, 0 ≤ K ∧ ∀ r j, |S.D.Ω r z j| ≤ K * (S.W r).w j) ∧
    (∀ z : WSeq V, flow S.D 0 z = z) ∧
    (∀ (t s : ι → ℝ) (z : WSeq V), flow S.D (t + s) z = flow S.D t (flow S.D s z)) ∧
    (∀ (t s : ι → ℝ) (z : WSeq V), flow S.D t (flow S.D s z) = flow S.D s (flow S.D t z)) ∧
    (∀ (t : ι → ℝ) (z : WSeq V) (j : ℤ), ‖(flow S.D t z).val j‖ = ‖z.val j‖) ∧
    (∀ (r : ι) (t : ι → ℝ) (z : WSeq V), S.F r (S.down r (flow S.D t z)) = S.F r (S.down r z)) ∧
    (∀ z : WSeq V, IsCompact (closure (Set.range fun t : ι → ℝ => flow S.D t z))) ∧
    Continuous (fun p : (ι → ℝ) × WSeq V => flow S.D p.1 p.2) ∧
    (∀ (s : ι → ℝ) (z : WSeq V)
      (hzP : ∀ k : ℕ, Summable fun j => V.w j * S.P j ^ (2 * k) * ‖z.val j‖ ^ 2),
      ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => flow S.D (τ • s) z) ∧
      ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => flow S.D (τ • s) z) (dcurve (S.hz_of s z hzP) 1 τ) τ) := by
  refine ⟨fun r z j => S.grad_eq r z j, fun r u z j => S.D.inv r u z j,
    fun z => S.freq_bound' z, fun z => flow_zero S.D z, fun t s z => flow_add S.D t s z,
    fun t s z => flow_comm S.D t s z, fun t z j => norm_flow_val S.D t z j, ?_,
    fun z => isCompact_orbit S.D z, continuous_flow S.D, ?_⟩
  · intro r t z
    obtain ⟨u, hu⟩ := flow_mem_torus S.D t z
    rw [← hu, S.down_rot, S.inv r]
  · intro s z hzP
    exact ⟨S.flow_smul_contDiff s z hzP, fun τ => S.flow_hasDerivAt s z hzP τ⟩

/-- On the DEF-002 scale `h^a`: every constant-action flow is `C^∞` in time for rapidly decreasing data. -/
theorem scale_flow_contDiff (L : ℝ) {ι : Type} [Fintype ι] (S : ι → ℝ) (hS : ∀ r, 0 ≤ S r) (a : ℝ)
    (ha : ∀ r, S r ≤ a) (F : ∀ r, h02 L (S r) → ℝ) (hF : ∀ r, ContDiff ℝ 2 (F r))
    (hinv : ∀ r (u : ℤ → Circle) (z : h02 L (S r)), F r (rot u z) = F r z)
    (s : ι → ℝ) (z : h02 L a) (hz : Hinf L z.val) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => flow (scaleData L S a ha F hF hinv).D (τ • s) z) :=
  (scaleData L S a ha F hF hinv).flow_smul_contDiff s z (hzP_of_Hinf L S hS a z.val hz)

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.seq_hierarchy
#print axioms QuantumNLS.RB7.scale_flow_contDiff
