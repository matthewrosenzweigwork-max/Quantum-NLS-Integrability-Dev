import Mathlib

/-!
# R-3FEAD88B blocker 2, stage E2b-i: real analysis for the periodic H^a algebra

Generic real lemmas on `ℤ`-indexed sequences, used by the convolution estimate
`hsq(c*d) ≤ K_a · hsq c · hsq d` (stage E2b, module `RiccatiSobolevE2b`):

* `cs_tsum`: real Cauchy-Schwarz for nonnegative tsums (Mathlib Hölder with p = q = 2);
* `young_summable_and_cs`: `(∑_j x_j y_{k-j})² ≤ (∑ y) · ∑_j x_j² y_{k-j}`, with summability;
* `young_tonelli`: `∑_k (∑_j x_j y_{k-j})² ≤ (∑ y)² · ∑ x²`, in `ENNReal`;
* `amgm_l1`, `l1_sq_le`: `(∑ x)² ≤ (∑ w⁻¹) · ∑ w x²` for positive weights;
* `rpow_add_le'`: Peetre-type bound `(x+y)^a ≤ 2^a (x^a + y^a)` for `a ≥ 0`;
* `tsum_shift_swap`: reindexing `∑_j f_j g_{k-j} = ∑_i g_i f_{k-i}`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.RiccatiSobolevE2bYoung

/-- Real Cauchy-Schwarz for tsums of nonnegative families, from Mathlib's Hölder inequality. -/
theorem cs_tsum {ι : Type*} (F G : ι → ℝ) (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i)
    (hF : Summable fun i => F i ^ 2) (hG : Summable fun i => G i ^ 2) :
    (∑' i, F i * G i) ^ 2 ≤ (∑' i, F i ^ 2) * ∑' i, G i ^ 2 := by
  have hF' : Summable fun i => F i ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hF
  have hG' : Summable fun i => G i ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hG
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := F) (g := G) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hF0 hG0 hF' hG'
  have hH' : ∑' i, F i * G i ≤ (∑' i, F i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, G i ^ 2) ^ (1 / 2 : ℝ) := by
    simpa only [Real.rpow_two] using hH
  have hX0 : 0 ≤ ∑' i, F i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hY0 : 0 ≤ ∑' i, G i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hnn : 0 ≤ ∑' i, F i * G i := tsum_nonneg fun i => mul_nonneg (hF0 i) (hG0 i)
  have hsqrt : ∀ X : ℝ, 0 ≤ X → (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    intro X hX
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    norm_num
  calc (∑' i, F i * G i) ^ 2
      ≤ ((∑' i, F i ^ 2) ^ (1 / 2 : ℝ) * (∑' i, G i ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hnn hH' 2
    _ = (∑' i, F i ^ 2) * ∑' i, G i ^ 2 := by
        rw [mul_pow, hsqrt _ hX0, hsqrt _ hY0]

/-- Reindexing a convolution sum: `∑_j f_j g_{k-j} = ∑_i g_i f_{k-i}` (no summability needed). -/
theorem tsum_shift_swap (f g : ℤ → ℝ) (k : ℤ) :
    ∑' j, f j * g (k - j) = ∑' i, g i * f (k - i) := by
  calc ∑' j, f j * g (k - j)
      = ∑' j, g ((Equiv.subLeft k) j) * f (k - (Equiv.subLeft k) j) :=
        tsum_congr fun j => by simp only [Equiv.subLeft_apply, sub_sub_cancel]; ring
    _ = ∑' i, g i * f (k - i) := Equiv.tsum_eq (Equiv.subLeft k) (fun i => g i * f (k - i))

/-- Pointwise Young `ℓ²·ℓ¹` estimate with summability, via Cauchy-Schwarz with weight `y`. -/
theorem young_summable_and_cs {x y : ℤ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hy1 : Summable y) (hx2 : Summable fun i => x i ^ 2) (k : ℤ) :
    Summable (fun j => x j * y (k - j)) ∧ Summable (fun j => x j ^ 2 * y (k - j)) ∧
    (∑' j, x j * y (k - j)) ^ 2 ≤ (∑' i, y i) * ∑' j, x j ^ 2 * y (k - j) := by
  have hyk : Summable (fun j => y (k - j)) := (Equiv.summable_iff (Equiv.subLeft k)).2 hy1
  have hxi : ∀ i, x i ^ 2 ≤ ∑' j, x j ^ 2 := fun i => hx2.le_tsum i (fun j _ => sq_nonneg _)
  have hbx : ∀ i, x i ≤ 1 + ∑' j, x j ^ 2 := fun i => by
    nlinarith [sq_nonneg (x i - 1 / 2), hxi i]
  have hs1 : Summable (fun j => x j * y (k - j)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hx j) (hy _))
      (fun j => mul_le_mul_of_nonneg_right (hbx j) (hy _)) (hyk.mul_left (1 + ∑' j, x j ^ 2))
  have hs2 : Summable (fun j => x j ^ 2 * y (k - j)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (hy _))
      (fun j => mul_le_mul_of_nonneg_right (hxi j) (hy _)) (hyk.mul_left (∑' j, x j ^ 2))
  have e1 : ∀ j, Real.sqrt (y (k - j)) ^ 2 = y (k - j) := fun j => Real.sq_sqrt (hy _)
  have e2 : ∀ j, (x j * Real.sqrt (y (k - j))) ^ 2 = x j ^ 2 * y (k - j) := fun j => by
    rw [mul_pow, e1]
  have e3 : ∀ j, Real.sqrt (y (k - j)) * (x j * Real.sqrt (y (k - j))) = x j * y (k - j) :=
    fun j => by
      have h := Real.mul_self_sqrt (hy (k - j))
      linear_combination x j * h
  have hcs := cs_tsum (fun j => Real.sqrt (y (k - j))) (fun j => x j * Real.sqrt (y (k - j)))
    (fun j => Real.sqrt_nonneg _) (fun j => mul_nonneg (hx j) (Real.sqrt_nonneg _))
    (by simpa only [e1] using hyk) (by simpa only [e2] using hs2)
  simp only [e1, e2, e3] at hcs
  have hshift : ∑' j, y (k - j) = ∑' i, y i := Equiv.tsum_eq (Equiv.subLeft k) y
  refine ⟨hs1, hs2, ?_⟩
  rw [hshift] at hcs
  exact hcs

/-- Summed Young estimate in `ENNReal`, with no summability assumption on the outer sum over `k`. -/
theorem young_tonelli {x y : ℤ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hy1 : Summable y) (hx2 : Summable fun i => x i ^ 2) :
    ∑' k, ENNReal.ofReal ((∑' j, x j * y (k - j)) ^ 2)
      ≤ ENNReal.ofReal (∑' i, y i) ^ 2 * ENNReal.ofReal (∑' i, x i ^ 2) := by
  have hY0 : 0 ≤ ∑' i, y i := tsum_nonneg hy
  have hX0 : 0 ≤ ∑' i, x i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hG0 : ∀ k, 0 ≤ ∑' j, x j ^ 2 * y (k - j) := fun k =>
    tsum_nonneg fun j => mul_nonneg (sq_nonneg _) (hy _)
  have hstep : ∀ k, ENNReal.ofReal ((∑' j, x j * y (k - j)) ^ 2)
      ≤ ENNReal.ofReal (∑' i, y i) * ∑' j, ENNReal.ofReal (x j ^ 2 * y (k - j)) := by
    intro k
    obtain ⟨-, hs2, hcs⟩ := young_summable_and_cs hx hy hy1 hx2 k
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hy _)) hs2,
      ← ENNReal.ofReal_mul hY0]
    exact ENNReal.ofReal_le_ofReal hcs
  have hcol : ∀ j, ∑' k, ENNReal.ofReal (x j ^ 2 * y (k - j))
      = ENNReal.ofReal (x j ^ 2) * ENNReal.ofReal (∑' i, y i) := by
    intro j
    have hshift : ∑' k, ENNReal.ofReal (y (k - j)) = ENNReal.ofReal (∑' i, y i) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hy hy1]
      exact (Equiv.subRight j).tsum_eq (fun i => ENNReal.ofReal (y i))
    have hmul : ∀ k, ENNReal.ofReal (x j ^ 2 * y (k - j))
        = ENNReal.ofReal (x j ^ 2) * ENNReal.ofReal (y (k - j)) :=
      fun k => ENNReal.ofReal_mul (sq_nonneg (x j))
    rw [tsum_congr hmul, ENNReal.tsum_mul_left, hshift]
  calc ∑' k, ENNReal.ofReal ((∑' j, x j * y (k - j)) ^ 2)
      ≤ ∑' k, ENNReal.ofReal (∑' i, y i) * ∑' j, ENNReal.ofReal (x j ^ 2 * y (k - j)) :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (∑' i, y i) * ∑' j, ∑' k, ENNReal.ofReal (x j ^ 2 * y (k - j)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
    _ = ENNReal.ofReal (∑' i, y i) * ∑' j, ENNReal.ofReal (x j ^ 2) * ENNReal.ofReal (∑' i, y i) := by
        congr 1
        exact tsum_congr hcol
    _ = ENNReal.ofReal (∑' i, y i) ^ 2 * ENNReal.ofReal (∑' i, x i ^ 2) := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg (x i)) hx2]
        ring

/-- AM-GM for a weighted square: `x ≤ (1/2)(w x² + w⁻¹)` for `w > 0`, `x ≥ 0`. -/
theorem amgm_l1 {w x : ℝ} (hw : 0 < w) : x ≤ (1 / 2) * (w * x ^ 2 + w⁻¹) := by
  have hw0 : w ≠ 0 := hw.ne'
  have key : w * x ^ 2 + w⁻¹ - 2 * x = w⁻¹ * (w * x - 1) ^ 2 := by
    field_simp <;> ring
  have hnn : 0 ≤ w⁻¹ * (w * x - 1) ^ 2 := mul_nonneg (inv_nonneg.2 hw.le) (sq_nonneg _)
  linarith

/-- The `ℓ¹` norm controlled by the weighted `ℓ²` norm: `(∑ x)² ≤ (∑ w⁻¹)(∑ w x²)`. -/
theorem l1_sq_le {w x : ℤ → ℝ} (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 ≤ x i)
    (hS : Summable fun i => (w i)⁻¹) (hH : Summable fun i => w i * x i ^ 2) :
    (∑' i, x i) ^ 2 ≤ (∑' i, (w i)⁻¹) * ∑' i, w i * x i ^ 2 := by
  have h1 : ∀ i, Real.sqrt ((w i)⁻¹) * Real.sqrt (w i) = 1 := fun i => by
    rw [← Real.sqrt_mul (inv_nonneg.2 (hw i).le), inv_mul_cancel₀ (hw i).ne', Real.sqrt_one]
  have e1 : ∀ i, Real.sqrt ((w i)⁻¹) * (Real.sqrt (w i) * x i) = x i := fun i => by
    linear_combination x i * h1 i
  have e2 : ∀ i, Real.sqrt ((w i)⁻¹) ^ 2 = (w i)⁻¹ := fun i =>
    Real.sq_sqrt (inv_nonneg.2 (hw i).le)
  have e3 : ∀ i, (Real.sqrt (w i) * x i) ^ 2 = w i * x i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hw i).le]
  have hc := cs_tsum (fun i => Real.sqrt ((w i)⁻¹)) (fun i => Real.sqrt (w i) * x i)
    (fun i => Real.sqrt_nonneg _) (fun i => mul_nonneg (Real.sqrt_nonneg _) (hx i))
    (by simpa only [e2] using hS) (by simpa only [e3] using hH)
  simp only [e1, e2, e3] at hc
  exact hc

/-- Peetre-type splitting: `(x + y)^a ≤ 2^a (x^a + y^a)` for `x, y ≥ 0` and `a ≥ 0`. -/
theorem rpow_add_le' {x y a : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) :
    (x + y) ^ a ≤ 2 ^ a * (x ^ a + y ^ a) := by
  have h2 : (0 : ℝ) ≤ 2 ^ a := Real.rpow_nonneg (by norm_num) a
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ a ≤ (2 * y) ^ a := Real.rpow_le_rpow (by linarith) (by linarith) ha
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy] at h1
    have h3 : 0 ≤ 2 ^ a * x ^ a := mul_nonneg h2 (Real.rpow_nonneg hx a)
    nlinarith
  · have h1 : (x + y) ^ a ≤ (2 * x) ^ a := Real.rpow_le_rpow (by linarith) (by linarith) ha
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx] at h1
    have h3 : 0 ≤ 2 ^ a * y ^ a := mul_nonneg h2 (Real.rpow_nonneg hy a)
    nlinarith

end QuantumNLS.RiccatiSobolevE2bYoung

#print axioms QuantumNLS.RiccatiSobolevE2bYoung.young_tonelli
#print axioms QuantumNLS.RiccatiSobolevE2bYoung.l1_sq_le
#print axioms QuantumNLS.RiccatiSobolevE2bYoung.rpow_add_le'
#print axioms QuantumNLS.RiccatiSobolevE2bYoung.tsum_shift_swap
#print axioms QuantumNLS.RiccatiSobolevE2bYoung.amgm_l1
