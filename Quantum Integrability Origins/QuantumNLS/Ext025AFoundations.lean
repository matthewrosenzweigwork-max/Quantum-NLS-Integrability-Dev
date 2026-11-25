import Mathlib

/-!+# EXT-025, author A: named standard foundations

The exact twelve input records (including all consumers) are copied into
`implementation/review records/sol_ext_snapshots/Ext025A.contracts.json`.
The identifiers below name the mathematical foundation in the corresponding record.
Application constructions are separate theorems; the final receipt distinguishes
foundation coverage from any unproved application clause. No consumer theorem is
inferred merely from this file.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology InnerProductSpace WeakDual
open scoped ComplexConjugate

namespace QuantumNLS.Ext025A

/-- GP-01. A star subalgebra includes the constants and is closed under
complex conjugation. Its topological closure is the supremum-norm closure.
The common-phase quotient, separation by quadratics, and coherent-polynomial
realization in the application wrapper are additional mathematical obligations;
they are not descriptive prose and are not asserted by this theorem. -/
theorem «FIN-EXT025-GP-01» {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] (A : StarSubalgebra ℂ C(K, ℂ)) (hA : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- GP-02. Evaluation on the compact character space is an isometric
star-algebra equivalence onto the continuous complex functions. -/
theorem «FIN-EXT025-GP-02» (A : Type*) [CommCStarAlgebra A] [Nontrivial A] :
    ∃ e : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ),
      Isometry e ∧ ∀ a χ, e a χ = χ a := by
  exact ⟨gelfandStarTransform A, gelfandTransform_isometry A, fun _ _ => rfl⟩

/-- GP-06. Riesz representation with uniqueness and the exact norm.
For complex scalars the representing-vector map is conjugate linear;
`InnerProductSpace.toDual` is a semilinear isometry equivalence. -/
theorem «FIN-EXT025-GP-06» {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (ℓ : E →L[𝕜] 𝕜) :
    (∃! v : E, ∀ w : E, inner 𝕜 v w = ℓ w) ∧
      ‖(toDual 𝕜 E).symm ℓ‖ = ‖ℓ‖ := by
  refine ⟨⟨(toDual 𝕜 E).symm ℓ, fun _ => toDual_symm_apply, ?_⟩,
    (toDual 𝕜 E).symm.norm_map ℓ⟩
  intro v hv
  apply (toDual 𝕜 E).injective
  ext w
  simpa using hv w

section SymplecticNormalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- GP-06 application, the source's real gradient convention:
if `dF(w) = Re ⟪g,w⟫`, then `X = -(i/2) g` satisfies
`2 Im ⟪X,w⟫ = dF(w)`. The factor two is explicit. -/
theorem gp06_hamiltonian_normalization (ℓ : E →L[ℝ] ℝ) (w : E) :
    2 * (inner ℂ (((-Complex.I) / 2) • (toDual ℝ E).symm ℓ) w).im = ℓ w := by
  rw [inner_smul_left]
  have hr : (inner ℂ ((toDual ℝ E).symm ℓ) w).re = ℓ w := by
    simpa only [real_inner_eq_re_inner, RCLike.re_to_complex] using
      (toDual_symm_apply (𝕜 := ℝ) (x := w) (y := ℓ))
  simp only [map_div₀, map_neg, Complex.conj_I, neg_neg,
    map_ofNat, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.I_re, Complex.I_im]
  linarith

/-- GP-06 application, the strong symplectic map is a bounded real-linear
isomorphism. It sends `v` to `w ↦ 2 Im ⟪v,w⟫`. Its inverse sends a real
functional with Riesz vector `g` to `-(i/2) g`. -/
theorem gp06_strong_symplectic_identification :
    ∃ J : E ≃L[ℝ] (E →L[ℝ] ℝ),
      (∀ v w, J v w = 2 * (inner ℂ v w).im) ∧
      ∀ ℓ, J.symm ℓ = ((-Complex.I) / 2) • (toDual ℝ E).symm ℓ := by
  let M : E ≃L[ℝ] E :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E)
      (Units.mk0 (2 * Complex.I : ℂ) (by simp))
  let J : E ≃L[ℝ] (E →L[ℝ] ℝ) := M.trans (toDual ℝ E).toContinuousLinearEquiv
  refine ⟨J, ?_, ?_⟩
  · intro v w
    change inner ℝ ((2 * Complex.I) • v) w = _
    rw [real_inner_eq_re_inner, RCLike.re_to_complex, inner_smul_left]
    simp [Complex.mul_re]
  · intro ℓ
    change (2 * Complex.I : ℂ)⁻¹ • (toDual ℝ E).symm ℓ = _
    congr 1
    norm_num [Complex.ext_iff, Complex.inv_re, Complex.inv_im, Complex.normSq]

end SymplecticNormalization
end QuantumNLS.Ext025A

#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-01»
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-02»
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-06»
#print axioms QuantumNLS.Ext025A.gp06_hamiltonian_normalization
#print axioms QuantumNLS.Ext025A.gp06_strong_symplectic_identification
