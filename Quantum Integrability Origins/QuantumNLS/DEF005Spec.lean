import QuantumNLS.ContactOperator
import QuantumNLS.CollisionIdentification

/-! integrator-authored trusted spec for DEF-005 (definitions.tex:31), contact form and collision
measure. For c ≥ 0 the contact form on H¹_sym(T_L^N) is Σ_j ‖∂_jψ‖² + 2c Σ_{j<k} ∫_{x_j=x_k} |ψ|² dy_jk,
with ∂_j the genuine weak derivative and dy_jk the coordinate measure on the remaining N−1 coordinates
(the collision trace is the literal restriction on smooth functions: C21SpecV2). The associated
self-adjoint operator is defined through the closed form (variational characterization, both
directions), not through a pointwise delta potential. -/

open MeasureTheory
open scoped InnerProductSpace
open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor
open QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification
open QuantumNLS.ContactForm QuantumNLS.ContactOperator

namespace QuantumNLS.DEF005Spec

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ) (hc : 0 ≤ c),
    -- form value with genuine weak derivatives and the physical dy_jk collision integral
    (∀ (ψ : PhysH1 L N) (G : Fin N → L2TN L N), (∀ j, HasWeakPartial j ψ.val (G j)) →
        q c ψ ψ = ((∑ j, ‖G j‖ ^ 2 + 2 * c * ∑ p : Pair N,
          ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) ψ‖ ^ 2 : ℝ) : ℂ)) ∧
    -- nonnegative
    (∀ ψ : PhysH1 L N, 0 ≤ (q c ψ ψ).re) ∧
    -- closed on H¹_sym (form-norm Cauchy sequences converge in form norm)
    (∀ u : ℕ → PhysH1 L N, (∀ n, u n ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) →
        (∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) →
        ∃ x : PhysH1 L N, x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
          Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0)) ∧
    -- densely defined: H¹_sym dense in the symmetric L²
    DenseRange (valSym : VSym L N →L[ℂ] SymL2 L N) ∧
    -- associated self-adjoint operator through the form
    IsSelfAdjoint (Hop (L := L) (N := N) c hc) ∧
    (∀ ψ : (Hop (L := L) (N := N) c hc).domain, ∃ x : VSym L N,
        (valSym x : SymL2 L N) = ψ ∧
        ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), Hop c hc ψ⟫_ℂ) ∧
    (∀ (x : VSym L N) (f : SymL2 L N),
        (∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ) →
        ∃ h : (valSym x : SymL2 L N) ∈ (Hop (L := L) (N := N) c hc).domain,
          Hop c hc ⟨valSym x, h⟩ = f)

theorem spec : Spec := by
  intro L _ N c hc
  refine ⟨?_, fun ψ => q_nonneg hc ψ, fun u hs hu => form_complete_sym hc u hs hu,
    denseRange_valSym, Hop_isSelfAdjoint hc, ?_, fun x f h => mem_domain_of_variational hc x f h⟩
  · intro ψ G hG
    rw [q_self]
    congr 2
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← gradientCLM_eq_of_weak j ψ (G j) (hG j)]
      have h := gradientCLM_inner j ψ ψ
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
      exact_mod_cast h.symm
    · refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
      have h := productTrace_inner p.1.1 p.1.2 (ne_of_lt p.2) ψ ψ
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
      exact_mod_cast h.symm
  · intro ψ
    have hd : (ψ : SymL2 L N) ∈ LinearMap.range (Rop (L := L) (N := N) c hc).toLinearMap := ψ.2
    obtain ⟨g, hg⟩ := hd
    refine ⟨psi c hc g, ?_, ?_⟩
    · rw [← Rop_eq_valSym_psi]; exact hg
    · intro φ
      obtain ⟨h, hH⟩ := Hop_Rop hc g
      have hψ : ψ = ⟨Rop c hc g, h⟩ := Subtype.ext hg.symm
      rw [hψ, variational_of_domain hc g φ]
      congr 1
      exact (eq_sub_of_add_eq hH).symm

end QuantumNLS.DEF005Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF005Spec.spec
  IO.println s!"DEF005Spec.spec axioms: {ax}"
