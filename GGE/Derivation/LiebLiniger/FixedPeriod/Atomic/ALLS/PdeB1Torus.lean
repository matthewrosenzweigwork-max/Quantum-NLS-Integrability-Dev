import Mathlib

/-! # Track B, step B1: the `L⁴` norm of a trigonometric polynomial on `ℝ/ℤ`

For a finitely supported coefficient family `c` (support in `S`), the trigonometric polynomial
`f = Σ_{k∈S} c_k e_k` on the period-one circle with normalized Haar measure satisfies
`∫ |f|⁴ = Σ_m |Σ_{k∈S} c_k c_{m-k}|²`. This is the spatial half of the physical-side identity
`‖v‖⁴_{L⁴(ℝ×𝕋)} = Σ_m ∫ |Σ_k v̂_k(t) v̂_{m-k}(t)|² dt` used in the proof of `X^{0,a} ↪ L⁴`.
Proof: `|f|⁴ = |f²|²`, expand `f²` in characters, compute its Fourier coefficients
(`fourierCoeff_fourier`), and apply Parseval (`tsum_sq_fourierCoeff`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory AddCircle

instance fact_zero_lt_one_real : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

/-- The trigonometric polynomial `Σ_{k∈S} c_k e_k` on `ℝ/ℤ`, as a continuous map. -/
def torusPoly (S : Finset ℤ) (c : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑ k ∈ S, c k • fourier k

theorem torusPoly_apply (S : Finset ℤ) (c : ℤ → ℂ) (x : AddCircle (1 : ℝ)) :
    torusPoly S c x = ∑ k ∈ S, c k * fourier k x := by
  simp [torusPoly, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]

/-- The square, expanded in characters. -/
theorem torusPoly_sq_apply (S : Finset ℤ) (c : ℤ → ℂ) (x : AddCircle (1 : ℝ)) :
    torusPoly S c x * torusPoly S c x =
      ∑ k ∈ S, ∑ j ∈ S, (c k * c j) * fourier (k + j) x := by
  rw [torusPoly_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [fourier_add]
  ring

/-- The square as a continuous map. -/
def torusPolySq (S : Finset ℤ) (c : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ∑ k ∈ S, ∑ j ∈ S, (c k * c j) • fourier (k + j)

theorem torusPolySq_apply (S : Finset ℤ) (c : ℤ → ℂ) (x : AddCircle (1 : ℝ)) :
    torusPolySq S c x = torusPoly S c x * torusPoly S c x := by
  rw [torusPoly_sq_apply]
  simp [torusPolySq, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]

/-- Fourier coefficients of the square: the discrete self-convolution. -/
theorem fourierCoeff_torusPolySq (S : Finset ℤ) (c : ℤ → ℂ) (hc : ∀ k ∉ S, c k = 0) (m : ℤ) :
    fourierCoeff (torusPolySq S c) m = ∑ k ∈ S, c k * c (m - k) := by
  have hint : ∀ (n : ℤ) (a : ℂ), Integrable (⇑(a • (fourier n : C(AddCircle (1 : ℝ), ℂ))))
      haarAddCircle := fun n a =>
    (a • (fourier n : C(AddCircle (1 : ℝ), ℂ))).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h1 : ⇑(torusPolySq S c) =
      ∑ k ∈ S, ⇑(∑ j ∈ S, (c k * c j) • (fourier (k + j) : C(AddCircle (1 : ℝ), ℂ))) := by
    simp only [torusPolySq, ContinuousMap.coe_sum]
  rw [h1, fourierCoeff.sum]
  swap
  · intro k _
    exact (∑ j ∈ S, (c k * c j) • (fourier (k + j) : C(AddCircle (1 : ℝ), ℂ))).continuous
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousMap.coe_sum, fourierCoeff.sum _ _ fun j _ => hint _ _, Finset.sum_apply]
  have h2 : ∀ j ∈ S, fourierCoeff (⇑((c k * c j) • (fourier (k + j) : C(AddCircle (1 : ℝ), ℂ)))) m
      = if j = m - k then c k * c j else 0 := by
    intro j _
    rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier]
    by_cases hj : j = m - k
    · subst hj
      simp
    · have : k + j ≠ m := fun h => hj (by omega)
      simp [Ne.symm this, hj]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [hc _ hm, mul_zero]

/-- **`L⁴` norm of a trigonometric polynomial**: `∫ |f|⁴ = Σ_m |Σ_{k∈S} c_k c_{m-k}|²`. -/
theorem integral_norm_pow_four_torusPoly (S : Finset ℤ) (c : ℤ → ℂ) (hc : ∀ k ∉ S, c k = 0) :
    ∫ x, ‖torusPoly S c x‖ ^ 4 ∂haarAddCircle = ∑' m : ℤ, ‖∑ k ∈ S, c k * c (m - k)‖ ^ 2 := by
  set g := torusPolySq S c
  have hpt : ∀ x, ‖torusPoly S c x‖ ^ 4 = ‖g x‖ ^ 2 := fun x => by
    rw [torusPolySq_apply, norm_mul]; ring
  simp_rw [hpt]
  set L := ContinuousMap.toLp (E := ℂ) 2 (haarAddCircle (T := 1)) ℂ g
  have hL : ∫ x, ‖g x‖ ^ 2 ∂haarAddCircle = ∫ x, ‖L x‖ ^ 2 ∂haarAddCircle :=
    integral_congr_ae ((ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) haarAddCircle g).mono
      fun x hx => by simp only [L]; rw [hx])
  rw [hL, ← tsum_sq_fourierCoeff L]
  congr 1
  funext m
  rw [fourierCoeff_toLp, fourierCoeff_torusPolySq S c hc m]

end LiebLiniger.FixedPeriod.ALLS.PdeB
