/-
QuantumNLS.RankTwoTrace — literal repair of step (S1) of R-828C5F7E `lem:fidelity`
(owner: opus_tensor).  Imports the frozen `QuantumNLS.Fidelity` (FD3, sha256 84f2a973…394ca)
read-only; FD3 is not modified.

Source (projective_reconstruction.tex:114–119, first paragraph of the proof of `lem:fidelity`):
  "For unit vectors v, z, the selfadjoint operator |v⟩⟨v| − |z⟩⟨z| vanishes on span{v,z}^⊥,
   has trace zero, and has square with trace 2(1 − |⟨v,z⟩|²). If its rank is two, its two
   eigenvalues are therefore ±√(1 − |⟨v,z⟩|²). If the span has dimension one the difference is
   zero. In both cases its trace norm is 2√(1 − |⟨v,z⟩|²)."

Lean route (follows the source step by step):
* `D = |v⟩⟨v| − |z⟩⟨z|` maps `K = span{v,z}` into itself.  Its restriction `D_K` is symmetric.
  `K` is finite-dimensional with `finrank K ≤ 2`.
* The finite-dimensional spectral theorem (mathlib `LinearMap.IsSymmetric.eigenvectorBasis`)
  gives an orthonormal eigenbasis `uᵢ` of `K` with real eigenvalues `λᵢ`.
* `D` vanishes on `K^⊥`, hence `D = Σᵢ λᵢ |uᵢ⟩⟨uᵢ|` on all of `E` (`D_eq_sum`).
* trace zero: `Σ λᵢ = 0` (`sum_eigenvalues`).
* trace of the square: `Σ λᵢ² = 2(1 − |⟨v,z⟩|²)` (`sum_sq_eigenvalues`).
* `‖Σ λᵢ |uᵢ⟩⟨uᵢ|‖₁ = Σ |λᵢ|` for orthonormal `uᵢ` (`traceNorm_diag`): trace norm = sum of
  absolute eigenvalues, with `|T| = Σ |λᵢ| |uᵢ⟩⟨uᵢ|` computed exactly.
* Dimension count `≤ 2` with the two trace identities gives the eigenvalues `±√(1−|⟨v,z⟩|²)`
  (rank two), or `0` (lower dimension).  Hence the EQUALITY
  `‖|v⟩⟨v| − |z⟩⟨z|‖₁ = 2√(1 − |⟨v,z⟩|²)` (`traceNorm_unit_sub_eq`).

Scope: this repairs S1 only.  The S2 frame-vs-spectral qualification of FD3 remains (see review record).
-/
import QuantumNLS.Fidelity
import Mathlib.Analysis.InnerProductSpace.Spectrum

open scoped InnerProductSpace ENNReal ComplexOrder
open QuantumNLS.TraceClass QuantumNLS.Fidelity

noncomputable section

namespace QuantumNLS.RankTwoTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Trace norm of a finite diagonal operator = sum of absolute eigenvalues -/

section Diagonal

variable {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u)

/-- `Σᵢ cᵢ |uᵢ⟩⟨uᵢ|`. -/
def diag (c : Fin n → ℂ) : E →L[ℂ] E :=
  ∑ i, c i • InnerProductSpace.rankOne ℂ (u i) (u i)

include hu in
omit [CompleteSpace E] in
theorem diag_mul_diag (c d : Fin n → ℂ) : diag u c * diag u d = diag u (c * d) := by
  classical
  simp only [diag, Finset.sum_mul, Finset.mul_sum, smul_mul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne, hu.1 i]
  · intro j _ hji
    simp [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne,
      orthonormal_iff_ite.mp hu, hji]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem star_diag_ofReal (r : Fin n → ℝ) :
    star (diag u (fun i => (r i : ℂ))) = diag u (fun i => (r i : ℂ)) := by
  simp only [diag, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

omit [CompleteSpace E] in
theorem isPositive_diag_nonneg (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (diag u (fun i => (r i : ℂ))).IsPositive :=
  ContinuousLinearMap.isPositive_sum _ fun i _ =>
    (InnerProductSpace.isPositive_rankOne_self (u i)).smul_of_nonneg
      (Complex.zero_le_real.mpr (hr i))

theorem posTrace_sum {ι : Type*} (s : Finset ι) (T : ι → E →L[ℂ] E)
    (hT : ∀ i, (T i).IsPositive) : posTrace (∑ i ∈ s, T i) = ∑ i ∈ s, posTrace (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [posTrace_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      posTrace_add (hT j) (ContinuousLinearMap.isPositive_sum s fun i _ => hT i), ih]

include hu in
/-- **Trace norm = Σ |eigenvalues|** for `Σᵢ rᵢ |uᵢ⟩⟨uᵢ|`, `uᵢ` orthonormal, `rᵢ` real. -/
theorem traceNorm_diag (r : Fin n → ℝ) :
    traceNorm (diag u (fun i => (r i : ℂ))) = ENNReal.ofReal (∑ i, |r i|) := by
  set T := diag u (fun i => (r i : ℂ))
  set B := diag u (fun i => ((|r i| : ℝ) : ℂ)) with hBdef
  have hB : B.IsPositive := isPositive_diag_nonneg u _ fun i => abs_nonneg _
  have hB0 : 0 ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr hB
  have habs : CFC.abs T = B := by
    have hTT : star T * T = B * B := by
      rw [star_diag_ofReal, diag_mul_diag u hu, diag_mul_diag u hu]
      congr 1
      funext i
      simp only [Pi.mul_apply]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
    rw [CFC.abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg T) hB0, hTT]
  have hP : ∀ i, posTrace (((|r i| : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (u i) (u i)) =
      ENNReal.ofReal |r i| := by
    intro i
    have hpos := (InnerProductSpace.isPositive_rankOne_self (u i)).smul_of_nonneg
      (Complex.zero_le_real.mpr (abs_nonneg (r i)))
    rw [← traceNorm_of_isPositive hpos, traceNorm_smul,
      traceNorm_of_isPositive (InnerProductSpace.isPositive_rankOne_self (u i)),
      posTrace_rankOne_self, hu.1 i, one_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs,
      ENNReal.ofReal_one, mul_one]
  rw [traceNorm, habs, hBdef, diag, posTrace_sum _ _ (fun i =>
      (InnerProductSpace.isPositive_rankOne_self (u i)).smul_of_nonneg
        (Complex.zero_le_real.mpr (abs_nonneg (r i)))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => hP i

end Diagonal

/-! ## Eigenvalue arithmetic: dimension `≤ 2`, trace zero, trace of square -/

/-- If `n ≤ 2`, `Σ λᵢ = 0` and `Σ λᵢ² = s`, then `Σ |λᵢ| = 2√(s/2)`
(rank two: eigenvalues `±√(s/2)`; lower rank: all zero). -/
theorem sum_abs_eq_of_le_two {n : ℕ} (hn : n ≤ 2) (l : Fin n → ℝ) {s : ℝ}
    (h1 : ∑ i, l i = 0) (h2 : ∑ i, l i ^ 2 = s) : ∑ i, |l i| = 2 * √(s / 2) := by
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at h2 ⊢
    rw [← h2]; simp
  · simp only [Fin.sum_univ_one] at h1 h2 ⊢
    rw [← h2, h1]; simp
  · simp only [Fin.sum_univ_two] at h1 h2 ⊢
    have hl1 : l 1 = -l 0 := by linarith
    rw [hl1] at h2 ⊢
    rw [← h2, abs_neg, show (l 0 ^ 2 + (-l 0) ^ 2) / 2 = l 0 ^ 2 by ring, Real.sqrt_sq_eq_abs]
    ring

/-! ## The rank-two operator `|v⟩⟨v| − |z⟩⟨z|` on `K = span{v, z}` -/

section RankTwo

variable (v z : E)

/-- `D = |v⟩⟨v| − |z⟩⟨z|`. -/
def rankTwo : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ z z

omit [CompleteSpace E] in
theorem rankTwo_apply (x : E) : rankTwo v z x = ⟪v, x⟫_ℂ • v - ⟪z, x⟫_ℂ • z := by
  simp [rankTwo, InnerProductSpace.rankOne_apply]

/-- `K = span{v, z}`. -/
def spanVZ : Submodule ℂ E := Submodule.span ℂ ({v, z} : Set E)

instance : FiniteDimensional ℂ (spanVZ v z) :=
  FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

omit [CompleteSpace E] in
theorem v_mem : v ∈ spanVZ v z := Submodule.subset_span (Set.mem_insert _ _)

omit [CompleteSpace E] in
theorem z_mem : z ∈ spanVZ v z := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

omit [CompleteSpace E] in
/-- `D` maps `K` into `K`. -/
theorem rankTwo_mapsTo : ∀ x ∈ spanVZ v z, rankTwo v z x ∈ spanVZ v z := fun x _ => by
  rw [rankTwo_apply]
  exact sub_mem (Submodule.smul_mem _ _ (v_mem v z)) (Submodule.smul_mem _ _ (z_mem v z))

omit [CompleteSpace E] in
/-- `dim K ≤ 2`. -/
theorem finrank_spanVZ_le : Module.finrank ℂ (spanVZ v z) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ℂ) ({v, z} : Finset E)
  have h2 : (({v, z} : Finset E) : Set E) = {v, z} := by simp
  rw [h2] at h
  exact h.trans Finset.card_le_two

omit [CompleteSpace E] in
/-- `D` is self-adjoint. -/
theorem rankTwo_isSymmetric : (rankTwo v z : E →ₗ[ℂ] E).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, rankTwo_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-- The restriction `D_K : K → K`. -/
def rankTwoK : spanVZ v z →ₗ[ℂ] spanVZ v z :=
  (rankTwo v z : E →ₗ[ℂ] E).restrict (rankTwo_mapsTo v z)

omit [CompleteSpace E] in
theorem rankTwoK_isSymmetric : (rankTwoK v z).IsSymmetric :=
  (rankTwo_isSymmetric v z).restrict_invariant (rankTwo_mapsTo v z)

/-- Orthonormal eigenbasis of `D_K` (finite-dimensional spectral theorem), viewed in `E`. -/
def eigvec (i : Fin (Module.finrank ℂ (spanVZ v z))) : E :=
  ((rankTwoK_isSymmetric v z).eigenvectorBasis rfl i : E)

/-- The real eigenvalues of `D_K`. -/
def eigval (i : Fin (Module.finrank ℂ (spanVZ v z))) : ℝ :=
  (rankTwoK_isSymmetric v z).eigenvalues rfl i

omit [CompleteSpace E] in
theorem eigvec_orthonormal : Orthonormal ℂ (eigvec v z) :=
  ((rankTwoK_isSymmetric v z).eigenvectorBasis rfl).orthonormal.comp_linearIsometry
    (spanVZ v z).subtypeₗᵢ

omit [CompleteSpace E] in
theorem eigvec_mem (i) : eigvec v z i ∈ spanVZ v z :=
  ((rankTwoK_isSymmetric v z).eigenvectorBasis rfl i).2

omit [CompleteSpace E] in
/-- `D uᵢ = λᵢ uᵢ`. -/
theorem rankTwo_eigvec (i) : rankTwo v z (eigvec v z i) = (eigval v z i : ℂ) • eigvec v z i := by
  have h := (rankTwoK_isSymmetric v z).apply_eigenvectorBasis rfl i
  have h2 := congrArg Subtype.val h
  simp only [rankTwoK, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h2
  exact h2

omit [CompleteSpace E] in
/-- Expansion of vectors of `K` in the eigenbasis. -/
theorem expand_mem {w : E} (hw : w ∈ spanVZ v z) :
    ∑ i, ⟪eigvec v z i, w⟫_ℂ • eigvec v z i = w := by
  have h := ((rankTwoK_isSymmetric v z).eigenvectorBasis rfl).sum_repr' ⟨w, hw⟩
  have h2 := congrArg (fun y : spanVZ v z => (y : E)) h
  simpa [Submodule.coe_sum, eigvec] using h2

omit [CompleteSpace E] in
/-- Parseval in `K`. -/
theorem parseval_mem {x y : E} (hx : x ∈ spanVZ v z) (hy : y ∈ spanVZ v z) :
    ∑ i, ⟪x, eigvec v z i⟫_ℂ * ⟪eigvec v z i, y⟫_ℂ = ⟪x, y⟫_ℂ :=
  ((rankTwoK_isSymmetric v z).eigenvectorBasis rfl).sum_inner_mul_inner ⟨x, hx⟩ ⟨y, hy⟩

omit [CompleteSpace E] in
/-- **`D` vanishes on `K^⊥` and is diagonal on `K`:** `D = Σᵢ λᵢ |uᵢ⟩⟨uᵢ|` on all of `E`. -/
theorem rankTwo_eq_diag :
    rankTwo v z = diag (eigvec v z) (fun i => (eigval v z i : ℂ)) := by
  ext x
  set y : E := ∑ i, ⟪eigvec v z i, x⟫_ℂ • eigvec v z i with hy
  have hperp : ∀ w ∈ spanVZ v z, ⟪w, x⟫_ℂ = ⟪w, y⟫_ℂ := by
    intro w hw
    have hx : ⟪w, x⟫_ℂ = ∑ i, ⟪w, eigvec v z i⟫_ℂ * ⟪eigvec v z i, x⟫_ℂ := by
      conv_lhs => rw [← expand_mem v z hw]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, inner_conj_symm]
    rw [hx, hy, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, mul_comm]
  have hDx : rankTwo v z x = rankTwo v z y := by
    rw [rankTwo_apply, rankTwo_apply, hperp v (v_mem v z), hperp z (z_mem v z)]
  rw [hDx, hy, map_sum, diag, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rankTwo_eigvec, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
    smul_comm]

omit [CompleteSpace E] in
theorem eigval_eq_inner (i) : (eigval v z i : ℂ) = ⟪eigvec v z i, rankTwo v z (eigvec v z i)⟫_ℂ := by
  rw [rankTwo_eigvec, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (eigvec_orthonormal v z).1 i]
  simp

omit [CompleteSpace E] in
/-- **Trace zero:** `Σ λᵢ = 0`. -/
theorem sum_eigval (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) : ∑ i, eigval v z i = 0 := by
  have h : (∑ i, (eigval v z i : ℂ)) = 0 := by
    simp_rw [eigval_eq_inner, rankTwo_apply, inner_sub_right, inner_smul_right]
    rw [Finset.sum_sub_distrib]
    have e1 := parseval_mem v z (v_mem v z) (v_mem v z)
    have e2 := parseval_mem v z (z_mem v z) (z_mem v z)
    rw [e1, e2, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv, hz, sub_self]
  exact_mod_cast h

omit [CompleteSpace E] in
/-- **Trace of the square:** `Σ λᵢ² = 2(1 − |⟨v,z⟩|²)`. -/
theorem sum_sq_eigval (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    ∑ i, eigval v z i ^ 2 = 2 - 2 * ‖⟪v, z⟫_ℂ‖ ^ 2 := by
  have hsq : ∀ i, ((eigval v z i ^ 2 : ℝ) : ℂ) =
      ⟪rankTwo v z (eigvec v z i), rankTwo v z (eigvec v z i)⟫_ℂ := by
    intro i
    rw [rankTwo_eigvec, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
      (eigvec_orthonormal v z).1 i, Complex.conj_ofReal]
    push_cast; ring
  have hexp : ∀ i, ⟪rankTwo v z (eigvec v z i), rankTwo v z (eigvec v z i)⟫_ℂ =
      ⟪v, eigvec v z i⟫_ℂ * ⟪eigvec v z i, v⟫_ℂ -
        ⟪v, z⟫_ℂ * (⟪z, eigvec v z i⟫_ℂ * ⟪eigvec v z i, v⟫_ℂ) -
        ⟪z, v⟫_ℂ * (⟪v, eigvec v z i⟫_ℂ * ⟪eigvec v z i, z⟫_ℂ) +
        ⟪z, eigvec v z i⟫_ℂ * ⟪eigvec v z i, z⟫_ℂ := by
    intro i
    have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
    have hzz : ⟪z, z⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hz]; simp
    rw [rankTwo_apply]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_conj_symm, hvv, hzz]
    ring
  have h : (∑ i, ((eigval v z i ^ 2 : ℝ) : ℂ)) = ((2 - 2 * ‖⟪v, z⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hsq, hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      parseval_mem v z (v_mem v z) (v_mem v z), parseval_mem v z (z_mem v z) (v_mem v z),
      parseval_mem v z (v_mem v z) (z_mem v z), parseval_mem v z (z_mem v z) (z_mem v z),
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv, hz,
      ← inner_conj_symm v z, Complex.conj_mul', Complex.mul_conj', RCLike.norm_conj]
    push_cast
    ring
  exact_mod_cast h

/-- **(S1), source form.** For unit `v, z`:
`‖|v⟩⟨v| − |z⟩⟨z|‖₁ = 2√(1 − |⟨v,z⟩|²)` (equality, via the eigenvalues). -/
theorem traceNorm_unit_sub_eq (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ z z) =
      ENNReal.ofReal (2 * √(1 - ‖⟪v, z⟫_ℂ‖ ^ 2)) := by
  change traceNorm (rankTwo v z) = _
  rw [rankTwo_eq_diag, traceNorm_diag _ (eigvec_orthonormal v z),
    sum_abs_eq_of_le_two (finrank_spanVZ_le v z) _ (sum_eigval v z hv hz)
      (sum_sq_eigval v z hv hz)]
  congr 2
  congr 1
  ring

/-- Consistency with FD2/FD3: the source equality yields exactly the statement of
`QuantumNLS.Fidelity.traceNorm_unit_sub_le` (proved there by the polarization route). -/
theorem traceNorm_unit_sub_le_via_eigenvalues (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - ‖⟪v, z⟫_ℂ‖ ^ 2)) :=
  (traceNorm_unit_sub_eq v z hv hz).le

end RankTwo

end QuantumNLS.RankTwoTrace

#print axioms QuantumNLS.RankTwoTrace.traceNorm_diag
#print axioms QuantumNLS.RankTwoTrace.rankTwo_eq_diag
#print axioms QuantumNLS.RankTwoTrace.sum_eigval
#print axioms QuantumNLS.RankTwoTrace.sum_sq_eigval
#print axioms QuantumNLS.RankTwoTrace.traceNorm_unit_sub_eq
