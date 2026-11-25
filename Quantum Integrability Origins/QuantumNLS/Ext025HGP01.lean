import QuantumNLS.Ext025AFoundations

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-01 = FIN-EXT025-GP-01
(complex Stone-Weierstrass on a compact phase quotient), stated at the literal
text of FINAL_EXTERNAL_THEOREM_INSTANCES.json:
  hypotheses: K compact Hausdorff; A a complex subalgebra of C(K) containing the
  constants, invariant under complex conjugation, separating distinct points;
  conclusion: A is dense in C(K) for the supremum norm.
The application wrapper of the record (quotient construction, coherent
polynomials) is consumer-side prose and is not part of this statement.
Proof: the frozen Ext025AFoundations.FIN-EXT025-GP-01 (star-subalgebra closure
equals the whole algebra, Mathlib Stone-Weierstrass) plus coercion bookkeeping. -/
noncomputable section
set_option autoImplicit false
open Set Topology

namespace QuantumNLS.Ext025HGP01

/-- Exact contract GP-01. -/
theorem contract_GP01 {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : A.SeparatesPoints) :
    Dense (A : Set C(K, ℂ)) := by
  let S : StarSubalgebra ℂ C(K, ℂ) := { A with star_mem' := fun {f} hf => hstar f hf }
  have hS : S.SeparatesPoints := hsep
  have htop : S.topologicalClosure = ⊤ :=
    QuantumNLS.Ext025A.«FIN-EXT025-GP-01» S hS
  have hcoe : (S.topologicalClosure : Set C(K, ℂ)) = closure (S : Set C(K, ℂ)) :=
    StarSubalgebra.topologicalClosure_coe S
  have hSA : (S : Set C(K, ℂ)) = (A : Set C(K, ℂ)) := rfl
  rw [htop, hSA] at hcoe
  have hcl : closure (A : Set C(K, ℂ)) = Set.univ := by
    rw [← hcoe]
    simp
  exact dense_iff_closure_eq.mpr hcl

end QuantumNLS.Ext025HGP01

#print axioms QuantumNLS.Ext025HGP01.contract_GP01
