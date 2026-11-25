import Mathlib
import QuantumNLS.RiccatiSobolevE1

/-!
# R-3FEAD88B blocker 2, stage E2a: summability of the inverse Sobolev weights (a > 1/2)

With the DEF-002 weights `wt L a k = (1 + |2πk/L|)^(2a)` (stage E1), the key input for the periodic
H^a algebra property (a > 1/2) is the convergence of `∑_k wt(k)⁻¹`. Proved here:

* `inv_wt_le`: `wt L a k⁻¹ ≤ (L/(2π))^(2a) |k|^(-(2a)) + [k = 0]` (pointwise, for `L > 0`);
* `summable_inv_wt`: `Summable (fun k : ℤ => (wt L a k)⁻¹)` for `1/2 < a`, via `Real.summable_abs_int_rpow`.

Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiSobolevE2

open QuantumNLS.RiccatiSobolevE1

theorem inv_wt_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (k : ℤ) :
    (wt L a k)⁻¹ ≤ (L / (2 * Real.pi)) ^ (2 * a) * |((k : ℤ) : ℝ)| ^ (-(2 * a))
      + (if k = 0 then (1 : ℝ) else 0) := by
  have hneg : -(2 * a) < 0 := by linarith
  by_cases hk : k = 0
  · subst hk
    simp [wt, freq, Real.zero_rpow hneg.ne]
  · have hk' : ((k : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk
    have hpos : 0 < |((k : ℤ) : ℝ)| := abs_pos.2 hk'
    have hfreq : |freq L k| = (2 * Real.pi / L) * |((k : ℤ) : ℝ)| := by
      unfold freq
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hL]
      ring
    have hA : 0 < 2 * Real.pi / L := by positivity
    have h1 : ((2 * Real.pi / L) * |((k : ℤ) : ℝ)|) ^ (2 * a) ≤ wt L a k := by
      unfold wt
      rw [← hfreq]
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (freq L k)]) (by linarith)
    have hX : 0 < ((2 * Real.pi / L) * |((k : ℤ) : ℝ)|) ^ (2 * a) :=
      Real.rpow_pos_of_pos (mul_pos hA hpos) _
    have h2 : (((2 * Real.pi / L) * |((k : ℤ) : ℝ)|) ^ (2 * a))⁻¹
        = (L / (2 * Real.pi)) ^ (2 * a) * |((k : ℤ) : ℝ)| ^ (-(2 * a)) := by
      rw [show L / (2 * Real.pi) = (2 * Real.pi / L)⁻¹ from (inv_div _ _).symm,
        Real.inv_rpow hA.le, Real.mul_rpow hA.le (abs_nonneg _), Real.rpow_neg (abs_nonneg _),
        mul_inv]
    have h3 : (wt L a k)⁻¹ ≤ (((2 * Real.pi / L) * |((k : ℤ) : ℝ)|) ^ (2 * a))⁻¹ :=
      inv_anti₀ hX h1
    rw [h2] at h3
    simpa [hk] using h3

theorem summable_inv_wt {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) :
    Summable (fun k : ℤ => (wt L a k)⁻¹) := by
  have hb : (1 : ℝ) < 2 * a := by linarith
  have hsum : Summable (fun k : ℤ =>
      (L / (2 * Real.pi)) ^ (2 * a) * |((k : ℤ) : ℝ)| ^ (-(2 * a))
        + (if k = 0 then (1 : ℝ) else 0)) :=
    ((Real.summable_abs_int_rpow hb).mul_left _).add ((hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable)
  exact Summable.of_nonneg_of_le (fun k => inv_nonneg.2 (wt_nonneg L a k))
    (fun k => inv_wt_le hL ha k) hsum

end QuantumNLS.RiccatiSobolevE2

#print axioms QuantumNLS.RiccatiSobolevE2.summable_inv_wt
