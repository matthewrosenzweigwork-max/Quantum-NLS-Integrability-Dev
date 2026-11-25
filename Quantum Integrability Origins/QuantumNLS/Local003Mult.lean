import Mathlib
import QuantumNLS.Local003Isometry
import QuantumNLS.TerraMultiRound25MatrixSpectrum
import QuantumNLS.Local002Domain

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage M5: the operator spectral multiplicity.

Source: "The two eigenvalues inside `Γ_n`, counted with operator multiplicity, are `a_n ± |b_n|`.  In particular they
coincide if and only if `b_n = 0`."

Statement proved (`operator_multiplicity`), for the actual operator `𝓛_u` on `𝓓_σ` (the graph `LuGraph`) and the actual
reduced map `B = reducedMatrix2`, whenever `B = [[a, b̄],[b, a]]`:
* for every `λ` with `|λ - p_n| < r`, the eigenspace `{f ∈ 𝓓_σ : 𝓛_u f = λ f}` is a linear subspace of `L²`
  whose complex dimension is the multiplicity of `λ` in the multiset `{a + |b|, a - |b|}`;
* `a ± |b|` lie strictly inside `Γ_n`.
Operator multiplicity is the dimension of the eigenspace of the self-adjoint operator (geometric multiplicity, which is
the multiplicity of the spectral projection); the finite-rank statement used is `rank P_n(u) = 2` (`proj_rank`, GP-17
route (ii)).  Proof: `eigen_P` (eigenvectors in the contour lie in `ran P`), `U` of `Local003Isometry`, and
`finrank (eigenspace B λ) = rootMultiplicity λ (charpoly B)` for Hermitian `B` (Mathlib, via semisimplicity), with
Terra's `charpoly_roots` (read-only). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Mult
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Rank
  QuantumNLS.Local002Free QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.Local003Range
  QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.LocalSpectral.Round27
  QuantumNLS.Local002Domain

variable {L κ r : ℝ}

/-! ### Linear algebra on `ℂ²` -/

lemma finrank_eigenspace_charpoly (B : E2 →L[ℂ] E2) (hB : ∀ v w, ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ) (lam : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam) =
      (B : E2 →ₗ[ℂ] E2).charpoly.rootMultiplicity lam := by
  have hsym : (B : E2 →ₗ[ℂ] E2).IsSymmetric := fun v w => hB v w
  rw [← LinearMap.finrank_maxGenEigenspace_eq,
    (hsym.isFinitelySemisimple).maxGenEigenspace_eq_eigenspace]

lemma charpoly_eq_matrix (a : ℝ) (b : ℂ) (B : E2 →L[ℂ] E2)
    (hab : ∀ v : E2, B v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1)) :
    (B : E2 →ₗ[ℂ] E2).charpoly = (Matrix.of ![![(a : ℂ), conj b], ![b, (a : ℂ)]]).charpoly := by
  let bs : Module.Basis (Fin 2) ℂ E2 := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  rw [← LinearMap.charpoly_toMatrix (B : E2 →ₗ[ℂ] E2) bs]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, bs, hab, vec2, EuclideanSpace.basisFun_apply]

/-- Geometric multiplicity for the explicit Hermitian matrix. -/
lemma finrank_eigenspace_form (a : ℝ) (b : ℂ) (B : E2 →L[ℂ] E2)
    (hB : ∀ v w, ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ)
    (hab : ∀ v : E2, B v = vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1)) (lam : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam) =
      Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} := by
  rw [finrank_eigenspace_charpoly B hB lam, charpoly_eq_matrix a b B hab,
    ← Polynomial.count_roots, QuantumNLS.TerraMultiRound25MatrixSpectrum.charpoly_roots]

/-! ### Eigenvectors on `ran P` -/

/-- An eigenvector of `𝓛_u` of nonzero norm with `P f = f` has its eigenvalue strictly inside the contour. -/
lemma eigen_inside (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) {f : H2 L} {lam : ℂ}
    (hf : (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n))
    (hPf : perturbedProj L κ (u : ℝ → ℂ) n r f = f) (hf0 : f ≠ 0) : ‖lam - center L n‖ < r := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  by_contra hge
  have hge : r ≤ ‖lam - center L n‖ := not_lt.mp hge
  have hne : ∀ z ∈ closedBall (center L n) r, z - lam ≠ 0 := by
    intro z hz hz0
    have hzr : ‖z - center L n‖ ≤ r := mem_closedBall_iff_norm.mp hz
    have : z = lam := sub_eq_zero.mp hz0
    rcases hge.eq_or_lt with h | h
    · -- `lam` on the contour: the resolvent exists there, forcing `f = 0`
      have hlam : lam ∈ sphere (center L n) r := mem_sphere_iff_norm.mpr h.symm
      have := (res_isRes hyp hr hr2 n u hq hlam).2 (f, lam • f) hf
      simp only [sub_self, map_zero] at this
      exact hf0 this.symm
    · rw [this] at hzr; linarith
  by_cases hon : ‖lam - center L n‖ = r
  · have hlam : lam ∈ sphere (center L n) r := mem_sphere_iff_norm.mpr hon
    have := (res_isRes hyp hr hr2 n u hq hlam).2 (f, lam • f) hf
    simp only [sub_self, map_zero] at this
    exact hf0 this.symm
  have hgt : r < ‖lam - center L n‖ := lt_of_le_of_ne hge (Ne.symm hon)
  have hne' : ∀ z ∈ closedBall (center L n) r, z - lam ≠ 0 := by
    intro z hz hz0
    have hzr : ‖z - center L n‖ ≤ r := mem_closedBall_iff_norm.mp hz
    have : z = lam := sub_eq_zero.mp hz0
    rw [this] at hzr; linarith
  have hpt : ∀ z ∈ sphere (center L n) r, resolvent L κ (u : ℝ → ℂ) (parity n) z f = (z - lam)⁻¹ • f := by
    intro z hz
    have := (res_isRes hyp hr hr2 n u hq hz).2 (f, lam • f) hf
    simp only at this
    rw [← sub_smul, map_smul] at this
    calc resolvent L κ (u : ℝ → ℂ) (parity n) z f
        = (z - lam)⁻¹ • ((z - lam) • resolvent L κ (u : ℝ → ℂ) (parity n) z f) := by
          rw [smul_smul, inv_mul_cancel₀ (hne' z (sphere_subset_closedBall hz)), one_smul]
      _ = (z - lam)⁻¹ • f := by rw [this]
  have hzero : ∮ z in C(center L n, r), (z - lam)⁻¹ • f = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      (f := fun z => (z - lam)⁻¹ • f) ?_ ?_
    · have hc : ContinuousOn (fun z : ℂ => z - lam) (closedBall (center L n) r) :=
        continuousOn_id.sub continuousOn_const
      exact (hc.inv₀ (fun z hz => hne' z hz)).smul continuousOn_const
    · intro z hz
      have hz' : z - lam ≠ 0 := hne' z (ball_subset_closedBall hz.1)
      exact ((differentiableAt_id.sub (differentiableAt_const lam)).inv hz').smul_const f
  have : perturbedProj L κ (u : ℝ → ℂ) n r f = 0 := by
    rw [P_apply hr hr2 n u hq, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz), hzero, smul_zero]
  rw [hPf] at this
  exact hf0 this

/-! ### The reduced matrix and the operator -/

section Main

variable {n : ℤ} {u : Lp ℂ 2 (μI L)}

local notation "PP" => perturbedProj L κ (u : ℝ → ℂ) n r
local notation "DD" => dressedIntegral L κ (u : ℝ → ℂ) n r
local notation "GG" => LuGraph L κ (u : ℝ → ℂ) (parity n)

/-- `D f + p_n f` is again in `ran P` when `f ∈ ran P`. -/
lemma X_inv (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (c : Ctx L κ r n u) (hL : 0 < L) {f : H2 L}
    (hf : PP f = f) : PP (DD f + (pm L n : ℂ) • f) = DD f + (pm L n : ℂ) • f := by
  have h := pair_mem hL hr hr2 n u c.hq c.hSA f
  rw [hf] at h
  have := P_Lu hr hr2 n u c.hq h
  rw [this, hf]

/-- For `P f = f`, `(f, λ f) ∈ Graph 𝓛_u` iff `D f + p_n f = λ f`. -/
lemma eigen_iff (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hL : 0 < L) (c : Ctx L κ r n u) {f : H2 L}
    (hf : PP f = f) (lam : ℂ) : (f, lam • f) ∈ GG ↔ DD f + (pm L n : ℂ) • f = lam • f := by
  have h := pair_mem hL hr hr2 n u c.hq c.hSA f
  rw [hf] at h
  constructor
  · intro h'
    exact LuGraph_functional hL h h'
  · intro h'
    rw [← h']; exact h

/-- A matrix eigenvector gives an operator eigenvector in `ran P`. -/
theorem graph_of_matrix (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hL : 0 < L) (c : Ctx L κ r n u) (lam : ℂ)
    (w : E2) (hw : w ∈ Module.End.eigenspace
      ((reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall : E2 →L[ℂ] E2) : E2 →ₗ[ℂ] E2) lam) :
    (Uf L κ (u : ℝ → ℂ) n r w, lam • Uf L κ (u : ℝ → ℂ) n r w) ∈ GG ∧
      PP (Uf L κ (u : ℝ → ℂ) n r w) = Uf L κ (u : ℝ → ℂ) n r w := by
  set U := Uf L κ (u : ℝ → ℂ) n r with hU
  have hUU := UUstar c
  have hU1 := UU_one c
  have hB : reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall = (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
      (ContinuousLinearMap.adjoint U) ∘L DD ∘L U := rfl
  have hUUx : ∀ x, U (ContinuousLinearMap.adjoint U x) = PP x := fun x =>
    congrArg (fun T : H2 L →L[ℂ] H2 L => T x) hUU
  have hU1x : ∀ w, ContinuousLinearMap.adjoint U (U w) = w := fun w =>
    congrArg (fun T : E2 →L[ℂ] E2 => T w) hU1
  rw [Module.End.mem_eigenspace_iff] at hw
  have hPf : PP (U w) = U w := by
    have := hUUx (U w)
    rw [hU1x] at this
    exact this.symm
  refine ⟨?_, hPf⟩
  rw [eigen_iff hr hr2 hL c hPf]
  have hXi := X_inv hr hr2 c hL hPf
  have hBw : reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall w = lam • w := hw
  rw [hB] at hBw
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply] at hBw
  have hUs : ContinuousLinearMap.adjoint U (DD (U w) + (pm L n : ℂ) • U w) = lam • w := by
    rw [map_add, map_smul, hU1x]
    have : ContinuousLinearMap.adjoint U (DD (U w)) = lam • w - (pm L n : ℂ) • w :=
      eq_sub_of_add_eq' hBw
    rw [this]; module
  calc DD (U w) + (pm L n : ℂ) • U w = PP (DD (U w) + (pm L n : ℂ) • U w) := hXi.symm
    _ = U (ContinuousLinearMap.adjoint U (DD (U w) + (pm L n : ℂ) • U w)) := (hUUx _).symm
    _ = lam • U w := by rw [hUs, map_smul]

/-- An operator eigenvector with eigenvalue inside the contour is `U` of a matrix eigenvector. -/
theorem matrix_of_graph (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hL : 0 < L) (c : Ctx L κ r n u) (lam : ℂ)
    (hlam : ‖lam - center L n‖ < r) {f : H2 L} (hf : (f, lam • f) ∈ GG) :
    ∃ w ∈ Module.End.eigenspace
      ((reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall : E2 →L[ℂ] E2) : E2 →ₗ[ℂ] E2) lam,
        Uf L κ (u : ℝ → ℂ) n r w = f := by
  set U := Uf L κ (u : ℝ → ℂ) n r with hU
  have hUU := UUstar c
  have hB : reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall = (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
      (ContinuousLinearMap.adjoint U) ∘L DD ∘L U := rfl
  have hUUx : ∀ x, U (ContinuousLinearMap.adjoint U x) = PP x := fun x =>
    congrArg (fun T : H2 L →L[ℂ] H2 L => T x) hUU
  have hPf := eigen_P hr hr2 n u c.hq hf hlam
  refine ⟨ContinuousLinearMap.adjoint U f, ?_, by rw [hUUx, hPf]⟩
  rw [Module.End.mem_eigenspace_iff]
  have hDf := (eigen_iff hr hr2 hL c hPf lam).1 hf
  have hUf : U (ContinuousLinearMap.adjoint U f) = f := by rw [hUUx, hPf]
  show reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall (ContinuousLinearMap.adjoint U f) =
    lam • ContinuousLinearMap.adjoint U f
  rw [hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, hUf]
  have : DD f = lam • f - (pm L n : ℂ) • f := eq_sub_of_add_eq hDf
  rw [this, map_sub, map_smul, map_smul]
  module

end Main

/-- **LOCAL-003, operator multiplicity.** -/
theorem operator_multiplicity (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hu : ‖u‖ < goodRadius κ L r) (a : ℝ) (b : ℂ)
    (hab : ∀ v : E2, reducedMatrix2 L κ (u : ℝ → ℂ) n r (ctx_of_ball hL hr hr2 n u hu).hsmall v =
      vec2 ((a : ℂ) * v 0 + conj b * v 1) (b * v 0 + (a : ℂ) * v 1)) :
    (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r →
      ∃ Eig : Submodule ℂ (H2 L),
        (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧
        Module.finrank ℂ Eig = Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)}) ∧
    ‖((a + ‖b‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧ ‖((a - ‖b‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r := by
  have c := ctx_of_ball hL hr hr2 n u hu
  set B := reducedMatrix2 L κ (u : ℝ → ℂ) n r c.hsmall with hBdef
  have hherm : ∀ v w, ⟪B v, w⟫_ℂ = ⟪v, B w⟫_ℂ := fun v w =>
    reducedMatrix2_hermitian hL hr hr2 n u c.hq c.hsmall v w
  have hcount := finrank_eigenspace_form a b B hherm hab
  have hUinj := U_inj c
  have hcen : (pm L n : ℂ) = center L n := rfl
  have hmem : ∀ lam : ℂ, 0 < Multiset.count lam {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} →
      ‖lam - (pm L n : ℂ)‖ < r := by
    intro lam hpos
    rw [← hcount] at hpos
    obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hw := x.2
    have hw0 : (x : E2) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨hG, hPf⟩ := graph_of_matrix hr hr2 hL c lam (x : E2) hw
    have hf0 : Uf L κ (u : ℝ → ℂ) n r (x : E2) ≠ 0 := by
      intro h
      exact hw0 (hUinj (by rw [h, map_zero]))
    rw [hcen]
    exact eigen_inside hr hr2 n u c.hq hG hPf hf0
  refine ⟨fun lam hlam => ?_,
    hmem _ (Multiset.count_pos.mpr (Multiset.mem_cons_self _ _)),
    hmem _ (Multiset.count_pos.mpr (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)))⟩
  refine ⟨Submodule.map (Uf L κ (u : ℝ → ℂ) n r : E2 →ₗ[ℂ] H2 L)
    (Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam), fun f => ?_, ?_⟩
  · rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (graph_of_matrix hr hr2 hL c lam w hw).1
    · intro hf
      exact matrix_of_graph hr hr2 hL c lam (by rwa [hcen] at hlam) hf
  · rw [← (Submodule.equivMapOfInjective (Uf L κ (u : ℝ → ℂ) n r : E2 →ₗ[ℂ] H2 L) hUinj
      (Module.End.eigenspace (B : E2 →ₗ[ℂ] E2) lam)).finrank_eq]
    exact hcount lam

end QuantumNLS.Local003Mult
#print axioms QuantumNLS.Local003Mult.finrank_eigenspace_form
#print axioms QuantumNLS.Local003Mult.eigen_inside
#print axioms QuantumNLS.Local003Mult.operator_multiplicity
