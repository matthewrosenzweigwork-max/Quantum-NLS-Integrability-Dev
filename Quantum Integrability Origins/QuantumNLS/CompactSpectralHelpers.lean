import Mathlib

/-!
# Compact self-adjoint spectral helper lemmas (EXT-001 helpers only)

Authorized scope (VERIFIED SCOPED OWNER APPROVAL, `implementation/ops/STATUS.md`, S2): the compact
spectral HELPER lemmas needed for EXT-001. This module states and proves NO continuity principle,
NO `AbstractContinuity`, and NO completeness claim for any concrete family. It is pure general
operator theory on a complex Hilbert space `E`, for a bounded operator `T` that is compact,
symmetric and (where stated) positive (`0 ≤ Re⟨Tx, x⟩`).

* `eig_apply`, `mem_eig`, `inner_eq_zero_of_eig` (eigenvectors of distinct real eigenvalues are
  orthogonal);
* mathlib links: `finiteDimensional_eigenspace` (nonzero eigenvalues of a compact operator have
  finite-dimensional eigenspaces) and `hasEigenvalue_iff_mem_spectrum'` (nonzero spectrum consists of
  eigenvalues);
* `finite_eigenvalues_above`: for `y > 0` only finitely many eigenvalues exceed `y`;
* `eigUp T y` (the span of eigenvectors with eigenvalue `> y`): finite dimensional
  (`finiteDimensional_eigUp`), `T`-invariant, and its orthogonal complement is `T`-invariant;
* level-`y` Rayleigh bounds: `lt_re_inner_of_mem_eigUp` (`Re⟨Tx,x⟩ > y‖x‖²` on `eigUp T y ∖ 0`) and,
  for positive `T`, `re_inner_le_of_mem_orth` (`Re⟨Tx,x⟩ ≤ y‖x‖²` on `(eigUp T y)ᗮ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.CompactSpectralHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## 1. Eigenvectors -/

lemma eig_apply {T : E →L[ℂ] E} {μ : ℂ} {w : E}
    (hw : w ∈ Module.End.eigenspace (T : Module.End ℂ E) μ) : T w = μ • w := by
  have := Module.End.mem_eigenspace_iff.1 hw
  simpa using this

lemma mem_eig {T : E →L[ℂ] E} {μ : ℂ} {w : E} (hw : T w = μ • w) :
    w ∈ Module.End.eigenspace (T : Module.End ℂ E) μ :=
  Module.End.mem_eigenspace_iff.2 (by simpa using hw)

/-- Eigenvectors of a symmetric operator for distinct real eigenvalues are orthogonal. -/
lemma inner_eq_zero_of_eig {T : E →L[ℂ] E} (hs : (T : E →ₗ[ℂ] E).IsSymmetric) {a b : ℝ}
    (hab : a ≠ b) {x z : E} (hx : T x = (a : ℂ) • x) (hz : T z = (b : ℂ) • z) : ⟪x, z⟫_ℂ = 0 := by
  have h := hs x z
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [hx, hz, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have : ((a : ℂ) - b) * ⟪x, z⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h1) hab
  · exact h1

theorem re_inner_real_smul (a : ℝ) (z : E) : RCLike.re ⟪(a : ℂ) • z, z⟫_ℂ = a * ‖z‖ ^ 2 := by
  rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex, Complex.re_ofReal_mul,
    ← RCLike.re_to_complex, inner_self_eq_norm_sq]

lemma eq_zero_of_mem_both {K : Submodule ℂ E} {z : E} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 :=
  inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2)

/-! ## 2. Links to mathlib's compact spectral theory -/

/-- Nonzero eigenvalues of a compact operator have finite-dimensional eigenspaces. -/
theorem finiteDimensional_eigenspace {T : E →L[ℂ] E} (hc : IsCompactOperator T) {μ : ℂ}
    (hμ : μ ≠ 0) : FiniteDimensional ℂ (Module.End.eigenspace (T : Module.End ℂ E) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ

/-- For a compact operator, a nonzero spectral value is an eigenvalue (and conversely). -/
theorem hasEigenvalue_iff_mem_spectrum' {T : E →L[ℂ] E} (hc : IsCompactOperator T) {μ : ℂ}
    (hμ : μ ≠ 0) : Module.End.HasEigenvalue (T : Module.End ℂ E) μ ↔ μ ∈ spectrum ℂ T :=
  hc.hasEigenvalue_iff_mem_spectrum hμ

/-! ## 3. Finitely many eigenvalues above a positive level -/

/-- The eigenvalues `> y`. -/
def eigSet (T : E →L[ℂ] E) (y : ℝ) : Set ℝ :=
  {μ : ℝ | y < μ ∧ Module.End.eigenspace (T : Module.End ℂ E) (μ : ℂ) ≠ ⊥}

/-- **For `y > 0`, a compact symmetric operator has only finitely many eigenvalues `> y`.** -/
theorem finite_eigenvalues_above {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : (T : E →ₗ[ℂ] E).IsSymmetric) {y : ℝ} (hy : 0 < y) : (eigSet T y).Finite := by
  by_contra hinf
  set S := eigSet T y
  let e := Set.Infinite.natEmbedding S hinf
  have hv : ∀ n, ∃ v : E, T v = (((e n : S) : ℝ) : ℂ) • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.1 (e n).2.2
    refine ⟨(‖w‖⁻¹ : ℂ) • w, ?_, ?_⟩
    · rw [map_smul, eig_apply hw, smul_comm]
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  choose v hvT hv1 using hv
  have hK := hc.isCompact_closure_image_closedBall 1
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n => T (v n))
    (fun n => subset_closure ⟨v n, by simp [hv1 n], rfl⟩)
  have hC := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hC
  obtain ⟨N, hN⟩ := hC y hy
  have hd := hN N le_rfl (N + 1) (Nat.le_succ N)
  simp only [Function.comp_apply] at hd
  set μ := ((e (φ N) : S) : ℝ)
  set μ' := ((e (φ (N + 1)) : S) : ℝ)
  have hne : μ ≠ μ' := by
    intro h
    have := e.injective (Subtype.ext h)
    exact absurd (hφ.injective this) (by omega)
  have horth := inner_eq_zero_of_eig hs hne (hvT (φ N)) (hvT (φ (N + 1)))
  have hμ : y < μ := (e (φ N)).2.1
  have hμ' : y < μ' := (e (φ (N + 1))).2.1
  rw [dist_eq_norm, hvT, hvT] at hd
  have hsq : ‖(μ : ℂ) • v (φ N) - (μ' : ℂ) • v (φ (N + 1))‖ ^ 2 = μ ^ 2 + μ' ^ 2 := by
    rw [@norm_sub_sq ℂ, inner_smul_left, inner_smul_right, horth, norm_smul, norm_smul,
      Complex.norm_real, Complex.norm_real, hv1, hv1]
    simp [sq_abs]
  have h1 : ‖(μ : ℂ) • v (φ N) - (μ' : ℂ) • v (φ (N + 1))‖ ^ 2 < y ^ 2 := by
    have h0 := norm_nonneg ((μ : ℂ) • v (φ N) - (μ' : ℂ) • v (φ (N + 1)))
    nlinarith
  nlinarith

/-! ## 4. The spectral subspace above level `y` -/

/-- `E_{>y}(T)`: the span of the eigenvectors of `T` with eigenvalue `> y`. -/
def eigUp (T : E →L[ℂ] E) (y : ℝ) : Submodule ℂ E :=
  ⨆ (μ : ℝ) (_ : y < μ), Module.End.eigenspace (T : Module.End ℂ E) (μ : ℂ)

lemma mem_eigUp {T : E →L[ℂ] E} {y μ : ℝ} (hμ : y < μ) {x : E} (hx : T x = (μ : ℂ) • x) :
    x ∈ eigUp T y :=
  (le_iSup₂ (f := fun (μ : ℝ) (_ : y < μ) => Module.End.eigenspace (T : Module.End ℂ E) (μ : ℂ))
    μ hμ) (mem_eig hx)

lemma eigUp_invariant (T : E →L[ℂ] E) (y : ℝ) : ∀ x ∈ eigUp T y, T x ∈ eigUp T y := by
  have h : eigUp T y ≤ (eigUp T y).comap (T : E →ₗ[ℂ] E) := by
    refine iSup₂_le fun μ hμ x hx => ?_
    show T x ∈ eigUp T y
    rw [eig_apply hx]
    exact Submodule.smul_mem _ _ (mem_eigUp hμ (eig_apply hx))
  exact fun x hx => h hx

/-- A vector orthogonal to every eigenvector with eigenvalue `> y` is in `(eigUp T y)ᗮ`. -/
lemma mem_orth_of_forall {T : E →L[ℂ] E} {y : ℝ} {z : E}
    (h : ∀ (μ : ℝ), y < μ → ∀ v, T v = (μ : ℂ) • v → ⟪z, v⟫_ℂ = 0) :
    z ∈ (eigUp T y)ᗮ := by
  have hle : eigUp T y ≤ (ℂ ∙ z)ᗮ := by
    refine iSup₂_le fun μ hμ v hv => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h μ hμ v (eig_apply hv)
  rw [Submodule.mem_orthogonal]
  intro v hv
  have h1 := (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hv)
  rw [← inner_conj_symm, h1, map_zero]

/-- The orthogonal complement of `eigUp T y` is `T`-invariant (`T` symmetric). -/
lemma orth_invariant {T : E →L[ℂ] E} (hs : (T : E →ₗ[ℂ] E).IsSymmetric) (y : ℝ) :
    ∀ x ∈ (eigUp T y)ᗮ, T x ∈ (eigUp T y)ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro v hv
  have := hs v x
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [← this]
  exact hx _ (eigUp_invariant T y v hv)

lemma eigUp_eq_finite (T : E →L[ℂ] E) (y : ℝ) :
    eigUp T y = ⨆ μ : eigSet T y, Module.End.eigenspace (T : Module.End ℂ E) ((μ : ℝ) : ℂ) := by
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    by_cases h : Module.End.eigenspace (T : Module.End ℂ E) (μ : ℂ) = ⊥
    · rw [h]; exact bot_le
    · exact le_iSup_of_le (⟨μ, hμ, h⟩ : eigSet T y) le_rfl
  · exact iSup_le fun μ => le_iSup₂_of_le (f := fun (μ : ℝ) (_ : y < μ) =>
      Module.End.eigenspace (T : Module.End ℂ E) (μ : ℂ)) μ.1 μ.2.1 le_rfl

/-- **`eigUp T y` is finite dimensional** for compact symmetric `T` and `y > 0`. -/
theorem finiteDimensional_eigUp {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : (T : E →ₗ[ℂ] E).IsSymmetric) {y : ℝ} (hy : 0 < y) :
    FiniteDimensional ℂ (eigUp T y) := by
  rw [eigUp_eq_finite]
  have : Finite (eigSet T y) := (finite_eigenvalues_above hc hs hy).to_subtype
  have : ∀ μ : eigSet T y, FiniteDimensional ℂ
      (Module.End.eigenspace (T : Module.End ℂ E) ((μ : ℝ) : ℂ)) := fun μ =>
    finiteDimensional_eigenspace hc
      (by exact_mod_cast (show (μ : ℝ) ≠ 0 from (hy.trans μ.2.1).ne'))
  exact Submodule.finiteDimensional_iSup _

/-! ## 5. Rayleigh bounds at level `y` -/

/-- **On `eigUp T y`, the Rayleigh quotient exceeds `y`.** -/
theorem lt_re_inner_of_mem_eigUp {T : E →L[ℂ] E} (hs : (T : E →ₗ[ℂ] E).IsSymmetric) {y : ℝ}
    [FiniteDimensional ℂ (eigUp T y)] {x : E} (hx : x ∈ eigUp T y) (hx0 : x ≠ 0) :
    y * ‖x‖ ^ 2 < RCLike.re ⟪T x, x⟫_ℂ := by
  set W := eigUp T y
  have hW0 : (⟨x, hx⟩ : W) ≠ 0 := fun h => hx0 (by simpa using congrArg Subtype.val h)
  have : Nontrivial W := nontrivial_of_ne _ _ hW0
  set T' : W →ₗ[ℂ] W := (T : E →ₗ[ℂ] E).restrict (eigUp_invariant T y)
  have hT' : T'.IsSymmetric := hs.restrict_invariant (eigUp_invariant T y)
  have hcoe : ∀ z : W, ((T' z : W) : E) = T z := fun z => rfl
  have hev := hT'.hasEigenvalue_iInf_of_finiteDimensional
  set m : ℝ := ⨅ z : {z : W // z ≠ 0}, RCLike.re ⟪T' z, z⟫_ℂ / ‖(z : W)‖ ^ 2 with hmdef
  obtain ⟨z0, hz0⟩ := hev.exists_hasEigenvector
  have hTz : T (z0 : E) = (m : ℂ) • (z0 : E) := by
    have h := Module.End.mem_eigenspace_iff.1 hz0.1
    have := congrArg Subtype.val h
    rw [hcoe] at this
    simpa using this
  have hz00 : (z0 : E) ≠ 0 := fun h => hz0.2 (Subtype.ext h)
  have hm : y < m := by
    by_contra hle
    push Not at hle
    have hz : (z0 : E) ∈ Wᗮ := mem_orth_of_forall fun μ hμ v hv =>
      inner_eq_zero_of_eig hs (by intro h; linarith) hTz hv
    exact hz00 (eq_zero_of_mem_both z0.2 hz)
  have hbdd : BddBelow (Set.range fun z : {z : W // z ≠ 0} =>
      RCLike.re ⟪T' z, z⟫_ℂ / ‖(z : W)‖ ^ 2) := by
    refine ⟨-‖T‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : 0 < ‖(z : W)‖ := norm_pos_iff.2 z.2
    rw [le_div_iff₀ (by positivity)]
    have h1 : |RCLike.re ⟪T' z, z⟫_ℂ| ≤ ‖T‖ * ‖(z : W)‖ ^ 2 := by
      calc |RCLike.re ⟪T' z, z⟫_ℂ| ≤ ‖⟪T' z, z⟫_ℂ‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖T' z‖ * ‖(z : W)‖ := norm_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖(z : W)‖ * ‖(z : W)‖ := by
            gcongr
            show ‖T (z : E)‖ ≤ ‖T‖ * ‖(z : E)‖
            exact T.le_opNorm _
        _ = _ := by ring
    have := neg_abs_le (RCLike.re ⟪T' z, z⟫_ℂ)
    nlinarith
  have hle := ciInf_le hbdd (⟨⟨x, hx⟩, hW0⟩ : {z : W // z ≠ 0})
  rw [← hmdef] at hle
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have e1 : RCLike.re ⟪T' ⟨x, hx⟩, ⟨x, hx⟩⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ := by
    rw [Submodule.coe_inner, hcoe]
  have e2 : ‖((⟨x, hx⟩ : W) : W)‖ = ‖x‖ := rfl
  simp only at hle
  rw [e1, e2, le_div_iff₀ (by positivity)] at hle
  nlinarith [mul_lt_mul_of_pos_right hm (pow_pos hxn 2)]

/-- A self-adjoint operator on a nontrivial Hilbert space has a spectral value of modulus `‖S‖`. -/
theorem exists_spectrum_norm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] [Nontrivial F] (S : F →L[ℂ] F) (hsa : IsSelfAdjoint S) :
    ∃ k ∈ spectrum ℂ S, ‖k‖ = ‖S‖ := by
  obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius S
  refine ⟨k, hk, ?_⟩
  rw [hsa.spectralRadius_eq_nnnorm, ENNReal.coe_inj] at hkn
  exact congrArg NNReal.toReal hkn

/-- **On `(eigUp T y)ᗮ`, the Rayleigh quotient is at most `y`** (`T` compact, symmetric, positive,
`y > 0`). -/
theorem re_inner_le_of_mem_orth {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : (T : E →ₗ[ℂ] E).IsSymmetric) (hp : ∀ x, 0 ≤ RCLike.re ⟪T x, x⟫_ℂ) {y : ℝ} (hy : 0 < y)
    {x : E} (hx : x ∈ (eigUp T y)ᗮ) : RCLike.re ⟪T x, x⟫_ℂ ≤ y * ‖x‖ ^ 2 := by
  by_contra hlt
  push Not at hlt
  set F := (eigUp T y)ᗮ
  have hF := orth_invariant hs y
  let S : F →L[ℂ] F := T.restrict hF
  have hS_compact : IsCompactOperator S := hc.restrict' hF
  have hS_symm : (S : F →ₗ[ℂ] F).IsSymmetric := hs.restrict_invariant hF
  have hScoe : ∀ z : F, ((S z : F) : E) = T z := fun z => rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hlt
  have hxF0 : (⟨x, hx⟩ : F) ≠ 0 := fun h => hx0 (by simpa using congrArg Subtype.val h)
  have : Nontrivial F := nontrivial_of_ne _ _ hxF0
  -- `‖S‖ > y`
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hSy : y < ‖S‖ := by
    have h1 : RCLike.re ⟪T x, x⟫_ℂ ≤ ‖S‖ * ‖x‖ ^ 2 := by
      calc RCLike.re ⟪T x, x⟫_ℂ ≤ ‖⟪T x, x⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
        _ = ‖S ⟨x, hx⟩‖ * ‖x‖ := rfl
        _ ≤ ‖S‖ * ‖(⟨x, hx⟩ : F)‖ * ‖x‖ := by gcongr; exact S.le_opNorm _
        _ = ‖S‖ * ‖x‖ ^ 2 := by rw [show ‖(⟨x, hx⟩ : F)‖ = ‖x‖ from rfl]; ring
    by_contra hle
    push Not at hle
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg ‖x‖)]
  -- a spectral value of modulus `‖S‖`
  have hsa : IsSelfAdjoint S := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hS_symm
  obtain ⟨k, hk, hknorm⟩ := exists_spectrum_norm S hsa
  have hk0 : k ≠ 0 := by
    intro h; rw [h, norm_zero] at hknorm; linarith [hy]
  obtain ⟨z, hz⟩ := ((hS_compact.hasEigenvalue_iff_mem_spectrum hk0).2 hk).exists_hasEigenvector
  have hSz : S z = k • z := by
    have := Module.End.mem_eigenspace_iff.1 hz.1
    simpa using this
  have hz0 : (z : E) ≠ 0 := fun h => hz.2 (Subtype.ext h)
  -- `k` is real and nonnegative
  have hkreal : conj k = k :=
    hS_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hz)
  have hkim : k.im = 0 := by
    have := congrArg Complex.im hkreal
    simp at this
    linarith
  have hkk : k = (k.re : ℂ) := Complex.ext rfl (by simp [hkim])
  have hTz : T (z : E) = (k.re : ℂ) • (z : E) := by
    rw [← hScoe, hSz, Submodule.coe_smul, ← hkk]
  have hkre : 0 ≤ k.re := by
    have h := hp (z : E)
    rw [hTz, re_inner_real_smul] at h
    have hzn : 0 < ‖(z : E)‖ ^ 2 := by have := norm_pos_iff.2 hz0; positivity
    nlinarith
  have hkS : k.re = ‖S‖ := by
    have h1 : ‖k‖ = |k.re| := by
      conv_lhs => rw [hkk]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← hknorm, h1, abs_of_nonneg hkre]
  -- `z` is an eigenvector of `T` with eigenvalue `> y`, hence in `eigUp T y ∩ (eigUp T y)ᗮ`
  have hzU : (z : E) ∈ eigUp T y := mem_eigUp (by rw [hkS]; exact hSy) hTz
  exact hz0 (eq_zero_of_mem_both hzU z.2)

/-! ## 6. Counting and comparison of levels -/

/-- **Comparison of level dimensions** (abstract form): if `q₁ ≤ q₂`, `q₁ > y‖·‖²` on `W₁ ∖ 0` and
`q₂ ≤ y‖·‖²` on `W₂ᗮ`, then `dim W₁ ≤ dim W₂`. -/
theorem finrank_le_of_forms (W₁ W₂ : Submodule ℂ E) [FiniteDimensional ℂ W₁]
    [FiniteDimensional ℂ W₂] (q₁ q₂ : E → ℝ) (y : ℝ) (hq : ∀ x, q₁ x ≤ q₂ x)
    (h1 : ∀ x ∈ W₁, x ≠ 0 → y * ‖x‖ ^ 2 < q₁ x) (h2 : ∀ x ∈ W₂ᗮ, q₂ x ≤ y * ‖x‖ ^ 2) :
    Module.finrank ℂ W₁ ≤ Module.finrank ℂ W₂ := by
  by_contra hlt
  push Not at hlt
  set f : W₁ →ₗ[ℂ] W₂ := (W₂.orthogonalProjectionOnto : E →ₗ[ℂ] W₂).comp W₁.subtype
  have hker := LinearMap.ker_ne_bot_of_finrank_lt hlt (f := f)
  obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.1 hker
  have hfx : W₂.orthogonalProjectionOnto (x : E) = 0 := hx
  have hxo : (x : E) ∈ W₂ᗮ := (Submodule.orthogonalProjectionOnto_eq_zero_iff).1 hfx
  have hx0' : (x : E) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have a := h1 x x.2 hx0'
  have b := h2 x hxo
  have c := hq x
  linarith

/-- **Monotonicity of the level counts**: if `T₁ ≤ T₂` in form order (both compact, symmetric, and
`T₂` positive) then `dim E_{>y}(T₁) ≤ dim E_{>y}(T₂)`, `y > 0`. -/
theorem finrank_eigUp_mono {T₁ T₂ : E →L[ℂ] E} (hc₁ : IsCompactOperator T₁)
    (hs₁ : (T₁ : E →ₗ[ℂ] E).IsSymmetric) (hc₂ : IsCompactOperator T₂)
    (hs₂ : (T₂ : E →ₗ[ℂ] E).IsSymmetric) (hp₂ : ∀ x, 0 ≤ RCLike.re ⟪T₂ x, x⟫_ℂ)
    (hle : ∀ x, RCLike.re ⟪T₁ x, x⟫_ℂ ≤ RCLike.re ⟪T₂ x, x⟫_ℂ) {y : ℝ} (hy : 0 < y) :
    haveI := finiteDimensional_eigUp hc₁ hs₁ hy
    haveI := finiteDimensional_eigUp hc₂ hs₂ hy
    Module.finrank ℂ (eigUp T₁ y) ≤ Module.finrank ℂ (eigUp T₂ y) := by
  have := finiteDimensional_eigUp hc₁ hs₁ hy
  have := finiteDimensional_eigUp hc₂ hs₂ hy
  exact finrank_le_of_forms _ _ (fun x => RCLike.re ⟪T₁ x, x⟫_ℂ) (fun x => RCLike.re ⟪T₂ x, x⟫_ℂ)
    y hle (fun x hx hx0 => lt_re_inner_of_mem_eigUp hs₁ hx hx0)
    (fun x hx => re_inner_le_of_mem_orth hc₂ hs₂ hp₂ hy hx)

/-- **Counting**: an independent family lying in a finite-dimensional subspace has at most
`dim` members, and if exactly `dim`, it spans. -/
theorem count_in_subspace (W : Submodule ℂ E) [FiniteDimensional ℂ W] {ι : Type*} (v : ι → E)
    (hli : LinearIndependent ℂ v) (J : Set ι) (hJ : ∀ i ∈ J, v i ∈ W) :
    J.Finite ∧ J.ncard ≤ Module.finrank ℂ W ∧
      (J.ncard = Module.finrank ℂ W → W ≤ Submodule.span ℂ (v '' J)) := by
  let w : J → W := fun i => ⟨v i, hJ i i.2⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp W.subtype
    exact hli.comp Subtype.val Subtype.val_injective
  have hfin : Finite J := hw.finite
  have hJf : J.Finite := Set.toFinite J
  have : Fintype J := hJf.fintype
  have hcard : J.ncard = Fintype.card J := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  refine ⟨hJf, hcard ▸ hw.fintype_card_le_finrank, fun heq => ?_⟩
  have hspan := hw.span_eq_top_of_card_eq_finrank' (hcard ▸ heq)
  intro x hx
  have h1 : (⟨x, hx⟩ : W) ∈ Submodule.span ℂ (Set.range w) := by rw [hspan]; trivial
  have h2 := Submodule.mem_map_of_mem (f := W.subtype) h1
  rw [Submodule.map_span] at h2
  have h3 : W.subtype '' Set.range w = v '' J := by
    ext z
    simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨w ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
  rw [h3] at h2
  exact h2

/-! ## 7. Eigenvector families -/

section Family

variable {T : E →L[ℂ] E} {ι : Type*} (v : ι → E) (μ : ι → ℝ)

lemma span_le_eig (hv : ∀ i, T (v i) = (μ i : ℂ) • v i) (lam : ℝ) (S : Set ι)
    (hS : ∀ i ∈ S, μ i = lam) :
    Submodule.span ℂ (v '' S) ≤ Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact mem_eig (by rw [hv i, hS i hi])

/-- **Projection to one eigenvalue**: an eigenvector (eigenvalue `λ`) in the span of a family of
eigenvectors lies in the span of the members with eigenvalue `λ`. -/
theorem mem_span_eigen_level (hs : (T : E →ₗ[ℂ] E).IsSymmetric)
    (hv : ∀ i, T (v i) = (μ i : ℂ) • v i) (K : Set ι) {x : E} {lam : ℝ}
    (hx : T x = (lam : ℂ) • x) (hxK : x ∈ Submodule.span ℂ (v '' K)) :
    x ∈ Submodule.span ℂ (v '' {i | i ∈ K ∧ μ i = lam}) := by
  set K₁ := {i | i ∈ K ∧ μ i = lam}
  set K₂ := {i | i ∈ K ∧ μ i ≠ lam}
  have hK : K = K₁ ∪ K₂ := by
    ext i; by_cases h : μ i = lam <;> simp [K₁, K₂, h]
  rw [hK, Set.image_union, Submodule.span_union] at hxK
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hxK
  have haE := span_le_eig v μ hv lam K₁ (fun i hi => hi.2) ha
  have hbE : b ∈ Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ) := by
    have h1 : a + b ∈ Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ) := mem_eig hx
    have := Submodule.sub_mem _ h1 haE
    simpa using this
  have hbO : b ∈ (Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ))ᗮ := by
    refine (Submodule.span_le.2 ?_) hb
    rintro _ ⟨i, ⟨_, hi⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal]
    intro u hu
    exact inner_eq_zero_of_eig hs (Ne.symm hi) (eig_apply hu) (hv i)
  rw [eq_zero_of_mem_both hbE hbO, add_zero]
  exact ha

/-- **A missing eigenvector**: if an eigenvector `x` (eigenvalue `λ ≠ 0`) of a compact symmetric
`T` is not in the span of the family members with eigenvalue `λ`, there is a nonzero eigenvector
for `λ` orthogonal to every member of the family. -/
theorem exists_orth_eigvec (hc : IsCompactOperator T) (hs : (T : E →ₗ[ℂ] E).IsSymmetric)
    (hv : ∀ i, T (v i) = (μ i : ℂ) • v i) {x : E} {lam : ℝ} (hlam : lam ≠ 0)
    (hx : T x = (lam : ℂ) • x) (hxn : x ∉ Submodule.span ℂ (v '' {i | μ i = lam})) :
    ∃ w : E, w ≠ 0 ∧ T w = (lam : ℂ) • w ∧ ∀ i, ⟪v i, w⟫_ℂ = 0 := by
  set W := Submodule.span ℂ (v '' {i | μ i = lam})
  have hWE := span_le_eig v μ hv lam {i | μ i = lam} (fun i hi => hi)
  have : FiniteDimensional ℂ (Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ)) :=
    finiteDimensional_eigenspace hc (by exact_mod_cast hlam)
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWE
  set w := x - W.starProjection x
  have hwO : w ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hwE : w ∈ Module.End.eigenspace (T : Module.End ℂ E) (lam : ℂ) :=
    Submodule.sub_mem _ (mem_eig hx) (hWE (W.starProjection_apply_mem x))
  refine ⟨w, fun h => hxn ?_, eig_apply hwE, fun i => ?_⟩
  · have : x = W.starProjection x := sub_eq_zero.1 h
    rw [this]; exact W.starProjection_apply_mem x
  · by_cases hi : μ i = lam
    · have hmem : v i ∈ W := Submodule.subset_span
        (Set.mem_image_of_mem v (show i ∈ {i | μ i = lam} from hi))
      exact Submodule.inner_right_of_mem_orthogonal hmem hwO
    · exact inner_eq_zero_of_eig hs hi (hv i) (eig_apply hwE)

/-- The level-`y` spanning property of an eigenvector family: every eigenvector of `T` with
eigenvalue `λ > y` is in the span of the members with eigenvalue `λ`. (A per-level, finite-rank
property; no completeness assertion.) -/
def FullAt (T : E →L[ℂ] E) (y : ℝ) : Prop :=
  ∀ (x : E) (lam : ℝ), y < lam → T x = (lam : ℂ) • x →
    x ∈ Submodule.span ℂ (v '' {i | μ i = lam})

/-- **Level-`y` spanning ⇔ counting**: for a compact symmetric `T`, `y > 0` and an independent
family of eigenvectors, the level-`y` spanning property holds iff the number of members with
eigenvalue `> y` equals `dim E_{>y}(T)`. -/
theorem fullAt_iff_count (hc : IsCompactOperator T) (hs : (T : E →ₗ[ℂ] E).IsSymmetric)
    (hli : LinearIndependent ℂ v) (hv : ∀ i, T (v i) = (μ i : ℂ) • v i) {y : ℝ} (hy : 0 < y) :
    haveI := finiteDimensional_eigUp hc hs hy
    (FullAt v μ T y ↔ {i | y < μ i}.ncard = Module.finrank ℂ (eigUp T y)) := by
  have := finiteDimensional_eigUp hc hs hy
  set J := {i | y < μ i}
  have hJmem : ∀ i ∈ J, v i ∈ eigUp T y := fun i hi => mem_eigUp hi (hv i)
  obtain ⟨hJf, hle, hspan⟩ := count_in_subspace (eigUp T y) v hli J hJmem
  constructor
  · intro hfull
    have hsub : eigUp T y ≤ Submodule.span ℂ (v '' J) := by
      refine iSup₂_le fun lam hlam x hx => ?_
      have h1 := hfull x lam hlam (eig_apply hx)
      refine Submodule.span_mono (Set.image_mono ?_) h1
      intro i hi
      show y < μ i
      rw [show μ i = lam from hi]; exact hlam
    have : Fintype (v '' J) := (hJf.image v).fintype
    have h2 : Module.finrank ℂ (eigUp T y) ≤ (v '' J).ncard := by
      have : FiniteDimensional ℂ (Submodule.span ℂ (v '' J)) :=
        FiniteDimensional.span_of_finite ℂ (hJf.image v)
      calc Module.finrank ℂ (eigUp T y) ≤ Module.finrank ℂ (Submodule.span ℂ (v '' J)) :=
            Submodule.finrank_mono hsub
        _ ≤ (v '' J).toFinset.card := finrank_span_le_card _
        _ = (v '' J).ncard := (Set.ncard_eq_toFinset_card' _).symm
    have h3 : (v '' J).ncard ≤ J.ncard := Set.ncard_image_le hJf
    omega
  · intro heq x lam hlam hx
    have hxJ := hspan heq (mem_eigUp hlam hx)
    have h1 := mem_span_eigen_level v μ hs hv J hx hxJ
    exact Submodule.span_mono (Set.image_mono fun i hi => hi.2) h1

end Family

/-! ## 8. Domination preserves compactness -/

/-- If `‖T₁x‖² ≤ Re⟨T₂x, x⟩` for all `x` and `T₂` is compact, then `T₁` is compact. -/
theorem isCompactOperator_of_dom {T₁ T₂ : E →L[ℂ] E} (hc : IsCompactOperator T₂)
    (h : ∀ x, ‖T₁ x‖ ^ 2 ≤ RCLike.re ⟪T₂ x, x⟫_ℂ) : IsCompactOperator T₁ := by
  show IsCompactOperator ((T₁ : E →ₗ[ℂ] E) : E → E)
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall (T₁ : E →ₗ[ℂ] E) one_pos]
  have hK : TotallyBounded (T₂ '' Metric.closedBall 0 1) :=
    (hc.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hA : TotallyBounded (T₁ '' Metric.closedBall 0 1) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨t, hts, htf, hcov⟩ :=
      Metric.finite_approx_of_totallyBounded hK (ε ^ 2 / 4) (by positivity)
    have hpre : ∀ y ∈ t, ∃ x ∈ Metric.closedBall (0 : E) 1, T₂ x = y := fun y hy => hts hy
    choose! g hg hgy using hpre
    refine ⟨T₁ '' (g '' t), (htf.image g).image T₁, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov ⟨x, hx, rfl⟩)
    refine Set.mem_iUnion₂.2 ⟨T₁ (g y), ⟨g y, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
    have hd : ‖x - g y‖ ≤ 2 := by
      have := norm_sub_le x (g y)
      have h1 := mem_closedBall_zero_iff.1 hx
      have h2 := mem_closedBall_zero_iff.1 (hg y hy)
      linarith
    have h2 : ‖T₂ (x - g y)‖ < ε ^ 2 / 4 := by
      rw [map_sub, hgy y hy, ← dist_eq_norm]; exact hxy
    have h3 : ‖T₁ (x - g y)‖ ^ 2 < ε ^ 2 := by
      calc ‖T₁ (x - g y)‖ ^ 2 ≤ RCLike.re ⟪T₂ (x - g y), x - g y⟫_ℂ := h _
        _ ≤ ‖⟪T₂ (x - g y), x - g y⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖T₂ (x - g y)‖ * ‖x - g y‖ := norm_inner_le_norm _ _
        _ ≤ ε ^ 2 / 4 * 2 := by gcongr
        _ < ε ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  exact isCompact_iff_totallyBounded_isComplete.2 ⟨hA.closure, isClosed_closure.isComplete⟩

#print axioms finite_eigenvalues_above
#print axioms finiteDimensional_eigUp
#print axioms lt_re_inner_of_mem_eigUp
#print axioms re_inner_le_of_mem_orth
#print axioms finrank_eigUp_mono
#print axioms count_in_subspace
#print axioms mem_span_eigen_level
#print axioms exists_orth_eigvec
#print axioms fullAt_iff_count
#print axioms isCompactOperator_of_dom

end QuantumNLS.CompactSpectralHelpers
