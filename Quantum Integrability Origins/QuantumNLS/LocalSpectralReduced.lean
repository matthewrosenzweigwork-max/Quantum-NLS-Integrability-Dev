import Mathlib
import QuantumNLS.LocalSpectralOperator

/-!
# DEF-049 repair: the compression, inverse square root and reduced matrix on `ℂ²`

Replaces the compression/normalization part of `LocalSpectralOperator` (sha256 314bbc00..., kept frozen), which
Terra r112 held for a real defect: `compression = P P_n(u) P` acts on the whole space `H_σ` and `invSqrt` used the
binomial series about the *whole-space* identity.  On the nonzero complement of `P` the compression is `0`, so
`T − 1 = −1` there, the series diverges and `tsum` silently returned its default `0`.

## Repair (as in `spectral_reduction.tex`, analytic-coordinate subsection)
`P H_σ` is first identified with `ℂ²` through the ordered basis `(χ_{n,1}, χ_{n,2})`, i.e. the embedding
`E = embed L n : ℂ² → H_σ`, and the inverse square root is taken *there*:
* `compressionMatrix L κ u n r = E* P_n(u) E` on `ℂ²`;
* `invSqrtM T = ∑_k binom(−1/2,k) (T − 1)^k` in `ℂ² →L ℂ²` (`invSqrtCoeff`);
* the hypothesis `SmallCompression L κ u n r : ‖C_n(u) − 1‖ < 1` is carried **as an explicit argument** of
  `invSqrtCompression`, `normalizedIsometry2` and `reducedMatrix2`, and `summable_invSqrtM` /
  `hasSum_invSqrtM` / `hasSum_invSqrtCompression` prove the series is summable (coefficients `|binom(−1/2,k)| ≤ 1`,
  `abs_invSqrtCoeff_le`, geometric bound), so no definition relies on a `tsum` default;
* `normalizedIsometry2 = P_n(u) E C_n(u)^{-1/2}`; `reducedMatrix2 = p_n 1 + U_n^*((2πi)⁻¹∮(z−p_n)(z−𝓛_u)⁻¹dz) U_n`.

## Proved (free consistency at `u = 0`)
* `inner_chi`, `adjoint_embed_comp_embed`: `(χ_{n,1}, χ_{n,2})` is orthonormal, `E* E = 1`;
* under the explicit hypothesis `hP : freeProj = E E*` (the free Riesz projection is the projection onto the
  span of `χ_{n,1}, χ_{n,2}`; this is the source's identification of the free spectral subspace and is **not**
  proved here): `compressionMatrix_zero : C_n(0) = 1`, `smallCompression_zero`, `invSqrtM_one : 1^{-1/2} = 1`,
  `normalizedIsometry2_zero : U_n = E`;
* under `hP` and the free resolvent hypothesis `hres` (every `z` on the contour is in the resolvent set of `𝓛_0`
  on `D_{(−1)^n}`): `resolvent_free_chi` (the resolvent acts by `(z−p_n)⁻¹` on `χ_{n,j}`),
  `dressedIntegral_free_embed` (the dressed contour integral kills `E ℂ²`), `reducedMatrix2_zero : B_n = p_n 1`.

## Still not claimed
Well-posedness for `u ≠ 0` (resolvent set contains the contours, `P_n(u)` rank two, `SmallCompression` itself,
common radius, analyticity) are theorem conclusions of the source.  `resolvent` still returns the junk value `0`
outside the resolvent set; the free theorems above carry the resolvent hypothesis `hres` explicitly.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace QuantumNLS.LocalSpectral

/-! ### Orthonormality of the ordered basis `(χ_{n,1}, χ_{n,2})` and `E* E = 1` -/

section Ortho

theorem inner_chi {L : ℝ} (hL : 0 < L) (n : ℤ) (i j : Fin 2) :
    ⟪chi L n i, chi L n j⟫_ℂ = if i = j then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hpt : ∀ᵐ x ∂μI L, ⟪(chi L n i : ℝ → E2) x, (chi L n j : ℝ → E2) x⟫_ℂ =
      if i = j then ((L⁻¹ : ℝ) : ℂ) else 0 := by
    filter_upwards [(memLp_chiFun L n i).coeFn_toLp, (memLp_chiFun L n j).coeFn_toLp] with x h1 h2
    have e1 : (chi L n i : ℝ → E2) x = chiFun L n i x := h1
    have e2 : (chi L n j : ℝ → E2) x = chiFun L n j x := h2
    rw [e1, e2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, norm_chiFun]
      have h : ((Real.sqrt L)⁻¹) ^ 2 = L⁻¹ := by rw [inv_pow, Real.sq_sqrt hL.le]
      rw [← RCLike.ofReal_pow, h]
      rfl
    · rw [if_neg hij]
      unfold chiFun
      simp [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left, hij]
  rw [integral_congr_ae hpt]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [integral_const]
    have hr : (μI L).real Set.univ = L := by
      simp [Measure.real, μI, Real.volume_Ioc, hL.le]
    rw [hr, Complex.real_smul]
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  · simp [hij]


theorem embed_apply (L : ℝ) (n : ℤ) (v : E2) : embed L n v = v 0 • chi L n 0 + v 1 • chi L n 1 := rfl

theorem inner_embed {L : ℝ} (hL : 0 < L) (n : ℤ) (v w : E2) :
    ⟪embed L n v, embed L n w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [embed_apply, embed_apply]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_chi hL]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- `E* E = 1`: the ordered basis `(χ_{n,1}, χ_{n,2})` is orthonormal. -/
theorem adjoint_embed_comp_embed {L : ℝ} (hL : 0 < L) (n : ℤ) :
    ContinuousLinearMap.adjoint (embed L n) ∘L embed L n = ContinuousLinearMap.id ℂ E2 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine ext_inner_left ℂ fun w => ?_
  simp [ContinuousLinearMap.adjoint_inner_right, inner_embed hL]

end Ortho

/-! ### Inverse square root on `ℂ²` (series about the identity) -/

section InvSqrt

theorem invSqrtCoeff_succ (k : ℕ) :
    invSqrtCoeff (k + 1) = invSqrtCoeff k * ((-(1 / 2 : ℝ) - k) / (k + 1)) := by
  unfold invSqrtCoeff
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp

theorem abs_invSqrtCoeff_le (k : ℕ) : |invSqrtCoeff k| ≤ 1 := by
  induction k with
  | zero => simp [invSqrtCoeff]
  | succ k ih =>
    rw [invSqrtCoeff_succ, abs_mul]
    have h : |(-(1 / 2 : ℝ) - k) / (k + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < k + 1), div_le_one (by positivity)]
      rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith [abs_nonneg (invSqrtCoeff k), abs_nonneg ((-(1 / 2 : ℝ) - k) / (k + 1))]

/-- The inverse square root series on `ℂ²`: `∑_k binom(−1/2,k) (T − 1)^k` (a genuine value only under
`‖T − 1‖ < 1`, see `hasSum_invSqrtM`). -/
def invSqrtM (T : E2 →L[ℂ] E2) : E2 →L[ℂ] E2 := ∑' k : ℕ, (invSqrtCoeff k : ℂ) • (T - 1) ^ k

theorem summable_invSqrtM {T : E2 →L[ℂ] E2} (h : ‖T - 1‖ < 1) :
    Summable fun k : ℕ => (invSqrtCoeff k : ℂ) • (T - 1) ^ k := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h) fun k => ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |invSqrtCoeff k| * ‖(T - 1) ^ k‖ ≤ 1 * ‖T - 1‖ ^ k :=
        mul_le_mul (abs_invSqrtCoeff_le k) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖T - 1‖ ^ k := one_mul _

theorem hasSum_invSqrtM {T : E2 →L[ℂ] E2} (h : ‖T - 1‖ < 1) :
    HasSum (fun k : ℕ => (invSqrtCoeff k : ℂ) • (T - 1) ^ k) (invSqrtM T) :=
  (summable_invSqrtM h).hasSum

theorem invSqrtM_one : invSqrtM 1 = 1 := by
  unfold invSqrtM
  rw [tsum_eq_single 0]
  · simp [invSqrtCoeff]
  · intro k hk
    rw [sub_self, zero_pow hk]
    exact ContinuousLinearMap.ext fun v => by simp

end InvSqrt

/-! ### The compression matrix on `ℂ²`, `U_n` and `B_n` (repaired definitions) -/

section Reduced

variable (L κ : ℝ)

/-- **The compression matrix** `C_n(u) = E* P_n(u) E` on `ℂ² ≅ P H` (`E = embed`, the ordered basis
`(χ_{n,1}, χ_{n,2})`). -/
def compressionMatrix (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  (ContinuousLinearMap.adjoint (embed L n)) ∘L (perturbedProj L κ u n r) ∘L (embed L n)

/-- Smallness hypothesis under which the inverse square root series is a genuine sum. -/
def SmallCompression (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : Prop :=
  ‖compressionMatrix L κ u n r - 1‖ < 1

/-- `C_n(u)^{-1/2}` on `ℂ²` (guarded by the smallness proof, so the series is summable). -/
def invSqrtCompression (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (_h : SmallCompression L κ u n r) :
    E2 →L[ℂ] E2 := invSqrtM (compressionMatrix L κ u n r)

theorem hasSum_invSqrtCompression (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (h : SmallCompression L κ u n r) :
    HasSum (fun k : ℕ => (invSqrtCoeff k : ℂ) • (compressionMatrix L κ u n r - 1) ^ k)
      (invSqrtCompression L κ u n r h) :=
  hasSum_invSqrtM h

/-- **The normalized isometry** `U_n = P_n(u) E C_n(u)^{-1/2} : ℂ² → H_σ`. -/
def normalizedIsometry2 (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (h : SmallCompression L κ u n r) :
    E2 →L[ℂ] H2 L :=
  (perturbedProj L κ u n r) ∘L (embed L n) ∘L (invSqrtCompression L κ u n r h)

/-- **The reduced matrix** `B_n = p_n 1 + U_n^* ((2πi)⁻¹∮(z−p_n)(z−𝓛_u)⁻¹dz) U_n`. -/
def reducedMatrix2 (u : ℝ → ℂ) (n : ℤ) (r : ℝ) (h : SmallCompression L κ u n r) : E2 →L[ℂ] E2 :=
  (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 +
    (ContinuousLinearMap.adjoint (normalizedIsometry2 L κ u n r h)) ∘L (dressedIntegral L κ u n r) ∘L
      (normalizedIsometry2 L κ u n r h)

variable {L κ}

theorem perturbedProj_zero (n : ℤ) (r : ℝ) :
    perturbedProj L κ (fun _ => 0) n r = freeProj L κ n r := rfl

/-- **Free consistency, `C_n(0) = 1`**, under the hypothesis that the free Riesz projection is `E E*`. -/
theorem compressionMatrix_zero (hL : 0 < L) (n : ℤ) (r : ℝ)
    (hP : freeProj L κ n r = embed L n ∘L ContinuousLinearMap.adjoint (embed L n)) :
    compressionMatrix L κ (fun _ => 0) n r = 1 := by
  have h1 : ∀ v, ContinuousLinearMap.adjoint (embed L n) (embed L n v) = v := fun v =>
    congrArg (fun T : E2 →L[ℂ] E2 => T v) (adjoint_embed_comp_embed hL n)
  refine ContinuousLinearMap.ext fun v => ?_
  show ContinuousLinearMap.adjoint (embed L n) (perturbedProj L κ (fun _ => 0) n r (embed L n v)) = v
  rw [perturbedProj_zero, hP]
  show ContinuousLinearMap.adjoint (embed L n) (embed L n (ContinuousLinearMap.adjoint (embed L n)
    (embed L n v))) = v
  rw [h1, h1]

theorem smallCompression_zero (hL : 0 < L) (n : ℤ) (r : ℝ)
    (hP : freeProj L κ n r = embed L n ∘L ContinuousLinearMap.adjoint (embed L n)) :
    SmallCompression L κ (fun _ => 0) n r := by
  unfold SmallCompression
  rw [compressionMatrix_zero hL n r hP]
  simp

/-- **Free consistency, `U_n = E`.** -/
theorem normalizedIsometry2_zero (hL : 0 < L) (n : ℤ) (r : ℝ)
    (hP : freeProj L κ n r = embed L n ∘L ContinuousLinearMap.adjoint (embed L n)) :
    normalizedIsometry2 L κ (fun _ => 0) n r (smallCompression_zero hL n r hP) = embed L n := by
  have h1 : ∀ v, ContinuousLinearMap.adjoint (embed L n) (embed L n v) = v := fun v =>
    congrArg (fun T : E2 →L[ℂ] E2 => T v) (adjoint_embed_comp_embed hL n)
  have hS : invSqrtCompression L κ (fun _ => 0) n r (smallCompression_zero hL n r hP) = 1 := by
    unfold invSqrtCompression
    rw [compressionMatrix_zero hL n r hP, invSqrtM_one]
  refine ContinuousLinearMap.ext fun v => ?_
  show perturbedProj L κ (fun _ => 0) n r (embed L n
    (invSqrtCompression L κ (fun _ => 0) n r (smallCompression_zero hL n r hP) v)) = embed L n v
  rw [hS, perturbedProj_zero, hP]
  show embed L n (ContinuousLinearMap.adjoint (embed L n) (embed L n v)) = embed L n v
  rw [h1]

end Reduced


section FreeB

variable {L κ : ℝ}

/-- On a free eigenfunction the resolvent acts by `(z − p_n)⁻¹`, when `z` is in the resolvent set. -/
theorem resolvent_free_chi (hL : 0 < L) (n : ℤ) (j : Fin 2) (z : ℂ)
    (hz : ∃ R, IsResolvent L κ (fun _ => 0) (parity n) z R) :
    (z - center L n) • resolvent L κ (fun _ => 0) (parity n) z (chi L n j) = chi L n j := by
  have hR : IsResolvent L κ (fun _ => 0) (parity n) z
      (resolvent L κ (fun _ => 0) (parity n) z) := by
    simp only [resolvent, dif_pos hz]; exact hz.choose_spec
  have h := hR.2 (chi L n j, (pm L n : ℂ) • chi L n j) (free_eigen hL κ n j)
  simp only at h
  rw [← sub_smul, map_smul] at h
  exact h

/-- On the contour, `(z − p_n)(z − 𝓛_0)⁻¹ E v = E v`, hence the dressed integral kills the free range. -/
theorem dressedIntegral_free_embed (hL : 0 < L) (n : ℤ) {r : ℝ} (hr : 0 < r)
    (hres : ∀ z : ℂ, ‖z - center L n‖ = r →
      ∃ R, IsResolvent L κ (fun _ => 0) (parity n) z R) (v : E2) :
    dressedIntegral L κ (fun _ => 0) n r (embed L n v) = 0 := by
  have hvec : ∀ z : ℂ, ‖z - center L n‖ = r →
      ((z - center L n) • resolvent L κ (fun _ => 0) (parity n) z) (embed L n v) = embed L n v := by
    intro z hz
    have e : ∀ j, (z - center L n) • resolvent L κ (fun _ => 0) (parity n) z (chi L n j) = chi L n j :=
      fun j => resolvent_free_chi hL n j z (hres z hz)
    rw [embed_apply, ContinuousLinearMap.smul_apply, map_add, map_smul, map_smul, smul_add,
      smul_comm (z - center L n) (v 0), smul_comm (z - center L n) (v 1), e, e]
  unfold dressedIntegral
  rw [ContinuousLinearMap.smul_apply]
  suffices h : (circleIntegral (fun z => (z - center L n) •
      resolvent L κ (fun _ => 0) (parity n) z) (center L n) r) (embed L n v) = 0 by
    rw [h, smul_zero]
  unfold circleIntegral
  beta_reduce
  by_cases hint : IntervalIntegrable (fun θ : ℝ => deriv (circleMap (center L n) r) θ •
      ((circleMap (center L n) r θ - center L n) •
        resolvent L κ (fun _ => 0) (parity n) (circleMap (center L n) r θ))) volume 0 (2 * Real.pi)
  · have h1 := (ContinuousLinearMap.apply ℂ (H2 L) (embed L n v)).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.apply_apply] at h1
    refine h1.symm.trans ?_
    refine (intervalIntegral.integral_congr (g := fun θ : ℝ => deriv (circleMap (center L n) r) θ •
      embed L n v) (fun θ _ => ?_)).trans ?_
    · show (deriv (circleMap (center L n) r) θ • ((circleMap (center L n) r θ - center L n) •
        resolvent L κ (fun _ => 0) (parity n) (circleMap (center L n) r θ))) (embed L n v) = _
      rw [ContinuousLinearMap.smul_apply,
        hvec _ (mem_sphere_iff_norm.mp (circleMap_mem_sphere _ hr.le θ))]
    · exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
        (f := fun _ => embed L n v) continuousOn_const (fun _ _ => differentiableAt_const _)
  · exact (congrArg (fun T : H2 L →L[ℂ] H2 L => T (embed L n v))
      (intervalIntegral.integral_undef hint)).trans (by simp)

/-- **Free consistency, `B_n = p_n · 1`** (under the free-projection hypothesis `P = E E*` and the free
resolvent hypothesis on the contour). -/
theorem reducedMatrix2_zero (hL : 0 < L) (n : ℤ) {r : ℝ} (hr : 0 < r)
    (hP : freeProj L κ n r = embed L n ∘L ContinuousLinearMap.adjoint (embed L n))
    (hres : ∀ z : ℂ, ‖z - center L n‖ = r →
      ∃ R, IsResolvent L κ (fun _ => 0) (parity n) z R) :
    reducedMatrix2 L κ (fun _ => 0) n r (smallCompression_zero hL n r hP) =
      (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2 := by
  unfold reducedMatrix2
  rw [normalizedIsometry2_zero hL n r hP]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [dressedIntegral_free_embed hL n hr hres v, map_zero, add_zero]

end FreeB

end QuantumNLS.LocalSpectral

#print axioms QuantumNLS.LocalSpectral.inner_chi
#print axioms QuantumNLS.LocalSpectral.adjoint_embed_comp_embed
#print axioms QuantumNLS.LocalSpectral.abs_invSqrtCoeff_le
#print axioms QuantumNLS.LocalSpectral.summable_invSqrtM
#print axioms QuantumNLS.LocalSpectral.invSqrtM_one
#print axioms QuantumNLS.LocalSpectral.compressionMatrix_zero
#print axioms QuantumNLS.LocalSpectral.normalizedIsometry2_zero
#print axioms QuantumNLS.LocalSpectral.dressedIntegral_free_embed
#print axioms QuantumNLS.LocalSpectral.reducedMatrix2_zero
