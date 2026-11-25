import Mathlib
import QuantumNLS.MixedLinearization
import QuantumNLS.KernelDefinition
import QuantumNLS.TraceClass

/-!
# PROP-026 remainder 1: the trace-norm form (general symmetric states) and the chart normalization

Imports `MixedLinearization` (f0fd9cb7, read-only) and the realized DEF-009 (`KernelDefinition`),
DEF-030 (`TensorCarrier.reducedDensityPower`) and `TraceClass`.  Closes the exact remaining statement 1 of
`MixedLinearization`, and part of statement 3.

## Proved
* **Trace identity for a GENERAL symmetric state** (generalizing DEF-009's `inner_U_N_r_product`, product states only).
  For `ψ ∈ Sym^{k+m}` (`SymSector ℂ E (k+m)`), `Ψ = splitIsometry k m ψ` and every bounded `S` on `E^{⊗̂k}`:
  `inner_U_eq_inner_htmap : ⟨ψ, 𝒰_{k+m,k}(P S P) ψ⟩ = ⟨Ψ, (S ⊗̂ 1) Ψ⟩`, with `P S P = symKernel S` the symmetrization
  (`extendSymKernel_symKernel`), via `htmap_symProj_split` (a symmetric vector is fixed by `P_k ⊗̂ 1`, from
  `splitIsometry_blockPerm_apply`) and `inner_htmap_symmetrize`.
* **The `Tr(J γ)` form**: `sum_inner_reducedDensity`: in every Hilbert basis `b` and for every finite `s`,
  `∑_{i∈s} ⟨T b_i, γ_Ψ b_i⟩ = ⟨(T P_s ⊗̂ 1)Ψ, Ψ⟩` with `γ_Ψ = reducedDensity Ψ` (DEF-030's
  `reducedDensityPower k m ψ = reducedDensity (split ψ)`).  Together: the finite partial traces of `T γ^{(k)}_ψ`
  against the symmetrized observable are the expectations `⟨ψ, 𝒰_{N,k}(·) ψ⟩`.  (The unrestricted infinite-sum `Tr(Jγ)`
  is not stated; only finite partial traces over a Hilbert basis are used, which is exactly what the realized duality
  `TraceClass.traceNorm_le_of_forall` needs.)
* **Trace-norm form from the observable form**: `traceNorm_reducedDensityPower_sub_le`: if
  `|⟨ψ₁,𝒰_{k+m,k}(J)ψ₁⟩ − ⟨ψ₂,𝒰_{k+m,k}(J)ψ₂⟩| ≤ c` for all contractions `J` on `Sym^k`, then
  `‖γ^{(k)}_{ψ₁} − γ^{(k)}_{ψ₂}‖₁ ≤ c`.
* **`prop026_traceNorm`**: PROP-026 in the source's trace-norm form, on `H = Sym^{k+q}E` (so `J_N = 𝒰_{N,k}(J)` is an
  operator on `H`): `‖γ^{(k)}_{e^{-iNC_{0,N}}φ} − γ^{(k)}_{e^{-iNL_N}φ}‖₁ ≤ C₀C₁M₀(∫ w δ dν) C_J`, with the same convention
  (operator-norm Bochner interpretation, hypotheses `hB hFm hdF` of PROP-014) and the same constants as
  `prop026_linearization`.  The commutator estimate `‖[B_{θ,j}, 𝒰_{N,k}(J)]‖ ≤ C_J/N` for contractions `J` stays an explicit
  hypothesis (`hJ`, remainder 2, not taken on).
* **Remainder 3, calculus part only**: `hasDerivAt_chartLambda`: for the chart of `eq:MP-chart`
  (`chartD`, `chartA`, `chartLambda`: Taylor/principal branches), `∂_wλ(z, s(z)) = D(z)⁻¹` when `D ≠ 0`, `s + D ≠ 0`,
  `A = (s+D)/2`.  This is the normalization the source uses to identify the linear part of `C_{0,N}` with `L_N`.

## Not done (exact remaining statements)
* `N` is written `k + q` (every `N ≥ k` is of this form); the `reducedDensityN`/`genericU_N_r` casts along
  `k + (N − k) = N` are not restated.
* Remainder 3 proper: identifying the abstract `F_θ`, `b_θ` with `f_z(S_N(z))`, `s(z)` (the DEF-048 transfer
  `S_N(z)` and its quadratures, the background `D, A, s` from the periodic basis) and `L_N` with `eq:MP-L` is not done; only
  `∂_wλ = D⁻¹` is.
* Remainder 2 (the commutator estimate) is untouched.
-/

set_option autoImplicit false

open scoped InnerProductSpace ENNReal ContDiff
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.PhysicalTensor
  QuantumNLS.KernelDefinition

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.MixedTraceNorm

/-! ### Finite trace form of the reduced density -/

section FiniteTrace

variable {X Y ι : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The finite partial projection `P_s = ∑_{i∈s} |b_i⟩⟨b_i|`. -/
def partialProj (b : HilbertBasis ι ℂ X) (s : Finset ι) : X →L[ℂ] X :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (b i) (b i)

theorem partialProj_apply (b : HilbertBasis ι ℂ X) (s : Finset ι) (x : X) :
    partialProj b s x = ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i := by
  simp [partialProj, ContinuousLinearMap.sum_apply]

theorem norm_partialProj_le (b : HilbertBasis ι ℂ X) (s : Finset ι) : ‖partialProj b s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [partialProj_apply, one_mul]
    exact QuantumNLS.TraceClass.norm_sum_inner_smul_le b s x

/-- **Finite trace form.**  `∑_{i∈s} ⟪T b_i, γ_Ψ b_i⟫ = ⟪(T ⊗̂ 1)·(P_s ⊗̂ 1) Ψ, Ψ⟫`. -/
theorem sum_inner_reducedDensity (b : HilbertBasis ι ℂ X) (s : Finset ι) (T : X →L[ℂ] X)
    (Ψ : HilbertTensor ℂ X Y) :
    ∑ i ∈ s, ⟪T (b i), reducedDensity Ψ (b i)⟫_ℂ =
      ⟪htmap (T ∘L partialProj b s) (ContinuousLinearMap.id ℂ Y) Ψ, Ψ⟫_ℂ := by
  have h1 : ∀ i, ⟪T (b i), reducedDensity Ψ (b i)⟫_ℂ =
      ⟪htmap (InnerProductSpace.rankOne ℂ (T (b i)) (b i)) (ContinuousLinearMap.id ℂ Y) Ψ, Ψ⟫_ℂ := by
    intro i
    rw [← inner_conj_symm (T (b i)) (reducedDensity Ψ (b i)), inner_reducedDensity_left,
      inner_conj_symm]
  simp_rw [h1]
  rw [← sum_inner, ← ContinuousLinearMap.sum_apply]
  congr 2
  have hsum : ∑ i ∈ s, htmap (InnerProductSpace.rankOne ℂ (T (b i)) (b i)) (ContinuousLinearMap.id ℂ Y) =
      htmap (∑ i ∈ s, InnerProductSpace.rankOne ℂ (T (b i)) (b i)) (ContinuousLinearMap.id ℂ Y) := by
    exact (map_sum (ampliate ℂ X Y) (fun i => InnerProductSpace.rankOne ℂ (T (b i)) (b i)) s).symm
  rw [hsum]
  congr 1
  ext x
  simp [partialProj, ContinuousLinearMap.sum_apply, map_sum, map_smul]

end FiniteTrace


/-! ### Reduction to symmetric kernels -/

section Sym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_symProjToSector_le (p : ℕ) (x : HilbertTensorPower ℂ E p) :
    ‖symProjToSector p x‖ ≤ ‖x‖ := by
  change ‖symProj ℂ E p x‖ ≤ ‖x‖
  rw [symProj_eq_starProjection]
  exact (SymSector ℂ E p).norm_starProjection_apply_le x

/-- The symmetrization `P S P` of an arbitrary operator, as a kernel on `Sym^p`. -/
def symKernel {p : ℕ} (S : HilbertTensorPower ℂ E p →L[ℂ] HilbertTensorPower ℂ E p) :
    SymSector ℂ E p →L[ℂ] SymSector ℂ E p :=
  (symProjToSector p).comp (S.comp (SymSector ℂ E p).subtypeL)

theorem norm_symKernel_le {p : ℕ} (S : HilbertTensorPower ℂ E p →L[ℂ] HilbertTensorPower ℂ E p) :
    ‖symKernel S‖ ≤ ‖S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun x => ?_
  calc ‖symKernel S x‖ = ‖symProjToSector p (S (x : HilbertTensorPower ℂ E p))‖ := rfl
    _ ≤ ‖S (x : HilbertTensorPower ℂ E p)‖ := norm_symProjToSector_le p _
    _ ≤ ‖S‖ * ‖(x : HilbertTensorPower ℂ E p)‖ := S.le_opNorm _
    _ = ‖S‖ * ‖x‖ := rfl

theorem extendSymKernel_symKernel {p : ℕ}
    (S : HilbertTensorPower ℂ E p →L[ℂ] HilbertTensorPower ℂ E p) :
    extendSymKernel (symKernel S) = symProj ℂ E p ∘L S ∘L symProj ℂ E p :=
  ContinuousLinearMap.ext fun _ => rfl

/-- A symmetric vector is fixed by `P_k ⊗̂ 1` in the split picture. -/
theorem htmap_symProj_split (k m : ℕ) (ψ : SymSector ℂ E (k + m)) :
    htmap (symProj ℂ E k) (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
      (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m))) =
      splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)) := by
  set Ψ := splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)) with hΨ
  have hσ : ∀ σ : Equiv.Perm (Fin k),
      htmap (permRep ℂ E k σ : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m)) Ψ = Ψ := by
    intro σ
    have h := splitIsometry_blockPerm_apply σ (1 : Equiv.Perm (Fin m))
      (ψ : HilbertTensorPower ℂ E (k + m))
    have hψ : permHilbertIsometry (blockPerm σ 1) (ψ : HilbertTensorPower ℂ E (k + m)) = ψ :=
      ψ.property (blockPerm σ 1)
    rw [hψ] at h
    have h1 : (permRep ℂ E m (1 : Equiv.Perm (Fin m)) :
        HilbertTensorPower ℂ E m →L[ℂ] HilbertTensorPower ℂ E m) = ContinuousLinearMap.id ℂ _ := by
      rw [map_one]; rfl
    rw [h1] at h
    exact h.symm
  rw [symProj_eq_factorial_average, htmap_smul_left]
  have hsum : htmap (∑ σ : Equiv.Perm (Fin k),
      (permRep ℂ E k σ : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k))
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m)) =
      ∑ σ : Equiv.Perm (Fin k), htmap
        (permRep ℂ E k σ : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m)) :=
    map_sum (ampliate ℂ (HilbertTensorPower ℂ E k) (HilbertTensorPower ℂ E m)) _ _
  rw [hsum]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, hσ, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k),
    one_smul]


theorem symProj_adjoint (p : ℕ) :
    ContinuousLinearMap.adjoint (symProj ℂ E p) = symProj ℂ E p :=
  (symProj_isStarProjection (𝕜 := ℂ) (E := E) p).isSelfAdjoint.adjoint_eq

theorem htmap_symProj_adjoint (k m : ℕ) :
    ContinuousLinearMap.adjoint (htmap (symProj ℂ E k)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))) =
      htmap (symProj ℂ E k) (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m)) := by
  rw [adjoint_htmap, symProj_adjoint, ContinuousLinearMap.adjoint_id]

/-- Symmetrizing the observable does not change its expectation in a symmetric state. -/
theorem inner_htmap_symmetrize (k m : ℕ) (S : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k)
    (ψ : SymSector ℂ E (k + m)) :
    ⟪splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)),
        htmap (extendSymKernel (symKernel S))
          (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ =
      ⟪splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)),
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ := by
  set Ψ := splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)) with hΨ
  set I := ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m) with hI
  set Hπ := htmap (symProj ℂ E k) I with hHπ
  have hfix : Hπ Ψ = Ψ := htmap_symProj_split k m ψ
  have hcomp : htmap (extendSymKernel (symKernel S)) I = Hπ ∘L (htmap S I ∘L Hπ) := by
    rw [extendSymKernel_symKernel]
    have h1 := htmap_comp (symProj ℂ E k) (S ∘L symProj ℂ E k) I I
    have h2 := htmap_comp S (symProj ℂ E k) I I
    simp only [hI, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at h1 h2 ⊢
    rw [h1, h2]
  rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hadj : ∀ x, ⟪Ψ, Hπ x⟫_ℂ = ⟪Hπ Ψ, x⟫_ℂ := by
    intro x
    have h := ContinuousLinearMap.adjoint_inner_left Hπ x Ψ
    rw [hHπ, htmap_symProj_adjoint] at h
    exact h.symm
  rw [hadj, hfix]

/-- **The trace identity for a general symmetric state**: for `ψ ∈ Sym^{k+m}` and an arbitrary bounded `S` on
`E^{⊗̂k}`, `⟨ψ, 𝒰_{k+m,k}(P S P) ψ⟩ = ⟨Ψ, (S ⊗̂ 1) Ψ⟩ = Tr(S γ^{(k)}_ψ)`-form (the last in the finite-basis
form `sum_inner_reducedDensity`), where `Ψ = split ψ` and `γ^{(k)}_ψ = reducedDensityPower k m ψ`. -/
theorem inner_U_eq_inner_htmap (k m : ℕ) (ψ : SymSector ℂ E (k + m))
    (S : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k) :
    ⟪ψ, U_N_r (r := k) (q := m) (symKernel S) ψ⟫_ℂ =
      ⟪splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)),
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ := by
  rw [← inner_htmap_symmetrize k m S ψ]
  set A := symKernel S with hA
  have h0 : ⟪ψ, U_N_r (r := k) (q := m) A ψ⟫_ℂ =
      ⟪(ψ : HilbertTensorPower ℂ E (k + m)), sandwichPlacement (q := m) A (ψ : HilbertTensorPower ℂ E (k + m))⟫_ℂ := rfl
  rw [h0]
  have hfix : symProj ℂ E (k + m) (ψ : HilbertTensorPower ℂ E (k + m)) = ψ :=
    groupAverage_apply_of_mem _ ψ.property
  have hadj : ∀ x : HilbertTensorPower ℂ E (k + m),
      ⟪(ψ : HilbertTensorPower ℂ E (k + m)), symProj ℂ E (k + m) x⟫_ℂ =
        ⟪symProj ℂ E (k + m) (ψ : HilbertTensorPower ℂ E (k + m)), x⟫_ℂ := by
    intro x
    have h := ContinuousLinearMap.adjoint_inner_left (symProj ℂ E (k + m)) x
      (ψ : HilbertTensorPower ℂ E (k + m))
    rw [symProj_adjoint] at h
    exact h.symm
  unfold sandwichPlacement
  simp only [ContinuousLinearMap.comp_apply]
  rw [hfix, hadj, hfix]
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply]
  set e := splitIsometry k m (E := E) (𝕜 := ℂ) with he
  show ⟪(ψ : HilbertTensorPower ℂ E (k + m)), e.symm (htmap (extendSymKernel A)
    (ContinuousLinearMap.id ℂ _) (e (ψ : HilbertTensorPower ℂ E (k + m))))⟫_ℂ = _
  rw [← e.inner_map_map, e.apply_symm_apply]

end Sym


/-! ### The trace-norm form -/

section TraceNormForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Trace-norm form from the observable form** (duality, `TraceClass.traceNorm_le_of_forall`).
If `|⟨ψ₁, 𝒰_{k+m,k}(J) ψ₁⟩ − ⟨ψ₂, 𝒰_{k+m,k}(J) ψ₂⟩| ≤ c` for every contraction `J` on `Sym^k`, then
`‖γ^{(k)}_{ψ₁} − γ^{(k)}_{ψ₂}‖₁ ≤ c` for symmetric `ψ₁, ψ₂ ∈ Sym^{k+m}`. -/
theorem traceNorm_reducedDensityPower_sub_le (k m : ℕ) (ψ₁ ψ₂ : SymSector ℂ E (k + m)) {c : ℝ}
    (h : ∀ J : SymSector ℂ E k →L[ℂ] SymSector ℂ E k, ‖J‖ ≤ 1 →
      ‖⟪ψ₁, U_N_r (r := k) (q := m) J ψ₁⟫_ℂ - ⟪ψ₂, U_N_r (r := k) (q := m) J ψ₂⟫_ℂ‖ ≤ c) :
    QuantumNLS.TraceClass.traceNorm
        (reducedDensityPower k m (ψ₁ : HilbertTensorPower ℂ E (k + m)) -
          reducedDensityPower k m (ψ₂ : HilbertTensorPower ℂ E (k + m))) ≤ ENNReal.ofReal c := by
  refine QuantumNLS.TraceClass.traceNorm_le_of_forall
    (QuantumNLS.TraceClass.refBasis (HilbertTensorPower ℂ E k)) _ fun X hX s => ?_
  set b := QuantumNLS.TraceClass.refBasis (HilbertTensorPower ℂ E k) with hb
  set S : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k := X ∘L partialProj b s with hS
  have hSn : ‖S‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    nlinarith [norm_partialProj_le b s, norm_nonneg (partialProj b s), norm_nonneg X]
  have hsum : ∑ i ∈ s, ⟪X (b i), (reducedDensityPower k m (ψ₁ : HilbertTensorPower ℂ E (k + m)) -
        reducedDensityPower k m (ψ₂ : HilbertTensorPower ℂ E (k + m))) (b i)⟫_ℂ =
      ⟪htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ₁ : HilbertTensorPower ℂ E (k + m))),
        splitIsometry k m (ψ₁ : HilbertTensorPower ℂ E (k + m))⟫_ℂ -
      ⟪htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ₂ : HilbertTensorPower ℂ E (k + m))),
        splitIsometry k m (ψ₂ : HilbertTensorPower ℂ E (k + m))⟫_ℂ := by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]
    rw [show reducedDensityPower k m (ψ₁ : HilbertTensorPower ℂ E (k + m)) =
        reducedDensity (splitIsometry k m (ψ₁ : HilbertTensorPower ℂ E (k + m))) from rfl,
      show reducedDensityPower k m (ψ₂ : HilbertTensorPower ℂ E (k + m)) =
        reducedDensity (splitIsometry k m (ψ₂ : HilbertTensorPower ℂ E (k + m))) from rfl,
      sum_inner_reducedDensity, sum_inner_reducedDensity]
  have hz : ∑ i ∈ s, ⟪X (b i), (reducedDensityPower k m (ψ₁ : HilbertTensorPower ℂ E (k + m)) -
        reducedDensityPower k m (ψ₂ : HilbertTensorPower ℂ E (k + m))) (b i)⟫_ℂ =
      (starRingEnd ℂ) (⟪ψ₁, U_N_r (r := k) (q := m) (symKernel S) ψ₁⟫_ℂ -
        ⟪ψ₂, U_N_r (r := k) (q := m) (symKernel S) ψ₂⟫_ℂ) := by
    rw [hsum, inner_U_eq_inner_htmap, inner_U_eq_inner_htmap, map_sub, inner_conj_symm,
      inner_conj_symm]
  have hJ : ‖symKernel S‖ ≤ 1 := (norm_symKernel_le S).trans hSn
  have hc := h (symKernel S) hJ
  rw [hz]
  show (Complex.re ((starRingEnd ℂ) _)) ≤ c
  rw [Complex.conj_re]
  exact (Complex.re_le_norm (⟪ψ₁, U_N_r (r := k) (q := m) (symKernel S) ψ₁⟫_ℂ -
    ⟪ψ₂, U_N_r (r := k) (q := m) (symKernel S) ψ₂⟫_ℂ)).trans hc

end TraceNormForm


/-! ### PROP-026 in the source's trace-norm form -/

section Prop026

open QuantumNLS.FunctionalLinearization

/-- **PROP-026 `lem:MP-linearization`, trace-norm form.**  On the symmetric sector `H = Sym^{k+q}E` (the
`N`-sector, `N = k + q`), for a normalized `φ`, the two evolved states `e^{-iNC_{0,N}}φ`, `e^{-iNL_N}φ` have
`k`-body reduced densities (DEF-030) with
`‖γ^{(k)}_{e^{-iNC_0}φ} − γ^{(k)}_{e^{-iNL}φ}‖₁ ≤ C₀C₁M₀ (∫ w δ dν) C_J`,
provided the commutator bound `‖[B_{θ,j}, 𝒰_{N,k}(J)]‖ ≤ C_J/N` holds for every contraction `J` on `Sym^k`
(`eq:MP-local-commutator`; **remainder 2, an explicit hypothesis**), and the deviation/derivative hypotheses of
`prop026_linearization`.  The constants are those of `prop026_linearization`. -/
theorem prop026_traceNorm (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : MeasureTheory.Measure Θ)
        [MeasureTheory.IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (k q : ℕ)
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (SymSector ℂ E (k + q) →L[ℂ] SymSector ℂ E (k + q)))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, MeasureTheory.AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : MeasureTheory.AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, MeasureTheory.AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (φ : SymSector ℂ E (k + q)) (hφ : ‖φ‖ = 1)
        (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hφδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) •
          (1 : SymSector ℂ E (k + q) →L[ℂ] SymSector ℂ E (k + q))) φ‖ ≤ δ θ)
        {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ J : SymSector ℂ E k →L[ℂ] SymSector ℂ E k, ‖J‖ ≤ 1 → ∀ θ j,
          ‖Φ θ (coordC j) * U_N_r (r := k) (q := q) J - U_N_r (r := k) (q := q) J * Φ θ (coordC j)‖ ≤
            CJ / N)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : MeasureTheory.Integrable w ν)
        (hwδ : MeasureTheory.Integrable (fun θ => w θ * δ θ) ν)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        QuantumNLS.TraceClass.traceNorm
          (reducedDensityPower k q
              ((evol ((N : ℂ) • C0N ν Φ F) 1 φ : SymSector ℂ E (k + q)) :
                HilbertTensorPower ℂ E (k + q)) -
            reducedDensityPower k q
              ((evol ((N : ℂ) • LN ν Φ F b) 1 φ : SymSector ℂ E (k + q)) :
                HilbertTensorPower ℂ E (k + q))) ≤
          ENNReal.ofReal ((C0 * (C1 * M0)) * (∫ θ, w θ * δ θ ∂ν) * CJ) := by
  obtain ⟨m, C0, hm, hC0, hmain⟩ := prop026_linearization d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {E} _ _ _ k q Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ
    {CJ} hCJ hJ w hw0 hw hwδ {M0} hM0 hFb => ?_⟩
  refine traceNorm_reducedDensityPower_sub_le k q _ _ fun J hJ1 => ?_
  exact hC1b ν Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN φ hφ δ hδ hφδ (U_N_r (r := k) (q := q) J) hCJ
    (hJ J hJ1) w hw0 hw hwδ hM0 hFb

end Prop026


/-! ### Remainder 3, the part that is a pure calculus fact: `∂_w λ(z, s(z)) = D(z)⁻¹` -/

section Chart

/-- The multiplier chart of `eq:MP-chart` at fixed `z`, as a function of the transfer value `w`:
`d(w) = D (1 + (w² − s²)/D²)^{1/2}` (principal/Taylor branch at `w = s`). -/
def chartD (D s w : ℂ) : ℂ := D * (1 + (w ^ 2 - s ^ 2) / D ^ 2) ^ (1 / 2 : ℂ)

/-- `a(w) = (w + d(w))/2`. -/
def chartA (D s w : ℂ) : ℂ := (w + chartD D s w) / 2

/-- `λ(w) = i κ G + log(a(w)/A)`, where `A = a(s) = (s + D)/2`; `c0` stands for the constant `iκ G(z)`. -/
def chartLambda (c0 D s A w : ℂ) : ℂ := c0 + Complex.log (chartA D s w / A)

theorem chartD_self {D : ℂ} (hD : D ≠ 0) (s : ℂ) : chartD D s s = D := by
  simp [chartD, Complex.one_cpow]

theorem chartA_self {D : ℂ} (hD : D ≠ 0) (s : ℂ) : chartA D s s = (s + D) / 2 := by
  simp [chartA, chartD_self hD]

/-- **`∂_w λ(z, s(z)) = D(z)⁻¹`** (the stated normalization of `eq:MP-chart`, used to identify the linear part
of `C_{0,N}` with `L_N`, `eq:MP-L`), for `D ≠ 0`, `s + D ≠ 0` and `A = (s + D)/2`. -/
theorem hasDerivAt_chartLambda (c0 : ℂ) {D s A : ℂ} (hD : D ≠ 0) (hsD : s + D ≠ 0)
    (hA : A = (s + D) / 2) : HasDerivAt (chartLambda c0 D s A) D⁻¹ s := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hg : HasDerivAt (fun w : ℂ => 1 + (w ^ 2 - s ^ 2) / D ^ 2) (2 * s / D ^ 2) s := by
    have h := ((hasDerivAt_pow 2 s).sub_const (s ^ 2)).div_const (D ^ 2) |>.const_add 1
    refine h.congr_deriv ?_
    simp
  have hg1 : (1 + (s ^ 2 - s ^ 2) / D ^ 2 : ℂ) ∈ Complex.slitPlane := by
    simp
  have hd : HasDerivAt (chartD D s) (s / D) s := by
    have h := (hg.cpow_const (c := (1 / 2 : ℂ)) hg1).const_mul D
    refine h.congr_deriv ?_
    simp [Complex.one_cpow]
    field_simp
  have ha : HasDerivAt (chartA D s) ((1 + s / D) / 2) s :=
    ((hasDerivAt_id s).add hd).div_const 2
  have hAne : A ≠ 0 := by rw [hA]; exact div_ne_zero hsD two_ne_zero
  have hq : HasDerivAt (fun w => chartA D s w / A) ((1 + s / D) / 2 / A) s := ha.div_const A
  have hone : chartA D s s / A = 1 := by rw [chartA_self hD, hA]; field_simp
  have hlog := (hq.clog (by rw [hone]; exact Complex.one_mem_slitPlane))
  have h2 := hlog.const_add c0
  refine h2.congr_deriv ?_
  rw [hone, div_one, hA]
  field_simp
  ring

end Chart

end QuantumNLS.MixedTraceNorm

#print axioms QuantumNLS.MixedTraceNorm.sum_inner_reducedDensity
#print axioms QuantumNLS.MixedTraceNorm.htmap_symProj_split
#print axioms QuantumNLS.MixedTraceNorm.inner_htmap_symmetrize
#print axioms QuantumNLS.MixedTraceNorm.inner_U_eq_inner_htmap
#print axioms QuantumNLS.MixedTraceNorm.traceNorm_reducedDensityPower_sub_le
#print axioms QuantumNLS.MixedTraceNorm.prop026_traceNorm
#print axioms QuantumNLS.MixedTraceNorm.hasDerivAt_chartLambda
