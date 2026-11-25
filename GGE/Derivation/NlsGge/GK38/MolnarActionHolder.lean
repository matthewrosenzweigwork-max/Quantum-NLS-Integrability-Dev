import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.GK38.MolnarBounds38

open Filter Topology

/-- Integer weighted Holder, including vanishing weights and the first moment. -/
theorem molnar_finite_weighted_holder38 {ι : Type*} (s : Finset ι) (m : ℕ)
    (hm : 1 ≤ m) (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ s, w i * f i) ^ m ≤
      (∑ i ∈ s, w i) ^ (m - 1) * (∑ i ∈ s, w i * f i ^ m) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h := Real.inner_le_weight_mul_Lp_of_nonneg s
    (show (1 : ℝ) ≤ m by exact_mod_cast hm) w f hw hf
  simp only [Real.rpow_natCast] at h
  have hM : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i _ => hw i
  have hA : 0 ≤ ∑ i ∈ s, w i * f i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hf i)
  have hX : 0 ≤ ∑ i ∈ s, w i * f i ^ m :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (pow_nonneg (hf i) _)
  have hp := pow_le_pow_left₀ hA h m
  rw [mul_pow] at hp
  have hleft : ((∑ i ∈ s, w i) ^ (1 - (m : ℝ)⁻¹)) ^ m =
      (∑ i ∈ s, w i) ^ (m - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    have he : (1 - (m : ℝ)⁻¹) * m = ((m - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hm, Nat.cast_one]
      field_simp
    rw [he, Real.rpow_natCast]
  have hright : ((∑ i ∈ s, w i * f i ^ m) ^ (m : ℝ)⁻¹) ^ m =
      ∑ i ∈ s, w i * f i ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX, inv_mul_cancel₀ hmp.ne', Real.rpow_one]
  rw [hleft, hright] at hp
  exact hp

/-- Genuine HasSum assumptions precede moment interpolation; no totalized divergent sum. -/
theorem molnar_weighted_holder_hasSum38 {ι : Type*} (m : ℕ) (hm : 1 ≤ m)
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i)
    (M A X : ℝ) (hM : HasSum w M) (hA : HasSum (fun i => w i * f i) A)
    (hX : HasSum (fun i => w i * f i ^ m) X) :
    A ^ m ≤ M ^ (m - 1) * X := by
  exact le_of_tendsto_of_tendsto' (hA.pow m) ((hM.pow (m - 1)).mul hX)
    (fun s => molnar_finite_weighted_holder38 s m hm w f hw hf)

end NlsGge.GK38.MolnarBounds38
