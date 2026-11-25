/- LIB-006 PRODUCTION01 (proof development review kit; HELD for landing). Source: proof development/LIB006_FINAL_V2.lean.txt
   (author proof development, request 1e12f95b; byte-identical except this header and the removed top-level `#print axioms` lines).
   Target NlsGge/Atomic/LIB/LIB006.lean, namespaces NlsGge.Atomic.LIB006 and NlsGge.Atomic.LIB005 (h1MulL2). -/
import Mathlib
import NlsGge.Atomic.LIB.LIB004
import NlsGge.Hierarchy.RiccatiPhysicalH1WeightedDerivativeSquareAfterRawHolderInnerPrerequisitesSecond

/-! LIB-006 step 1 (Mathlib-only): Fourier coefficients of a product of two L² functions on
`AddCircle T` are the absolutely summable convolution of their coefficients. Proof by Parseval
for the Fourier Hilbert basis, applied to `x = fourier n · conj v` and `y = u`. -/

open MeasureTheory AddCircle
open scoped ComplexConjugate InnerProductSpace

namespace NlsGge.Atomic.LIB006

variable {T : ℝ} [hT : Fact (0 < T)]

lemma inner_basis_eq_fourierCoeff (f : Lp ℂ 2 (@haarAddCircle T hT)) (i : ℤ) :
    ⟪fourierBasis i, f⟫_ℂ = fourierCoeff f i := by
  rw [← fourierBasis.repr_apply_apply f i, fourierBasis_repr]

lemma norm_fourier_le_one (n : ℤ) (t : AddCircle T) :
    ‖(fourier n : AddCircle T → ℂ) t‖ ≤ 1 := by
  have h := (fourier (T := T) n).norm_coe_le_norm t
  rwa [fourier_norm] at h

lemma conj_fourier_mul (n : ℤ) (t : AddCircle T) (a b : ℂ) :
    b * conj ((fourier n : AddCircle T → ℂ) t * star a) =
      (fourier (-n) : AddCircle T → ℂ) t * (a * b) := by
  rw [show star a = conj a from rfl, map_mul, Complex.conj_conj, ← fourier_neg]
  ring

theorem fourierCoeff_mul_hasSum (u v : Lp ℂ 2 (@haarAddCircle T hT)) (n : ℤ) :
    HasSum (fun k : ℤ => fourierCoeff u k * fourierCoeff v (n - k))
      (fourierCoeff (fun t => (u : AddCircle T → ℂ) t * (v : AddCircle T → ℂ) t) n) := by
  have hv : MemLp (fun t => (v : AddCircle T → ℂ) t) 2 (@haarAddCircle T hT) := Lp.memLp v
  have hmeas : AEStronglyMeasurable (fun t => (fourier n : AddCircle T → ℂ) t *
      star ((v : AddCircle T → ℂ) t)) (@haarAddCircle T hT) :=
    (fourier n).continuous.aestronglyMeasurable.mul (hv.aestronglyMeasurable.star)
  have hmem : MemLp (fun t => (fourier n : AddCircle T → ℂ) t *
      star ((v : AddCircle T → ℂ) t)) 2 (@haarAddCircle T hT) :=
    MemLp.of_le hv.norm hmeas (ae_of_all _ fun t => by
      rw [norm_mul, norm_star, norm_norm]
      nlinarith [norm_fourier_le_one n t, norm_nonneg ((v : AddCircle T → ℂ) t)])
  set x : Lp ℂ 2 (@haarAddCircle T hT) := hmem.toLp _ with hxdef
  have hx : ∀ᵐ t ∂(@haarAddCircle T hT), x t =
      (fourier n : AddCircle T → ℂ) t * star ((v : AddCircle T → ℂ) t) :=
    hmem.coeFn_toLp
  have hP := fourierBasis.hasSum_inner_mul_inner x u
  have h1 : ∀ i : ℤ, ⟪fourierBasis i, u⟫_ℂ = fourierCoeff u i :=
    fun i => inner_basis_eq_fourierCoeff u i
  have h2 : ∀ i : ℤ, ⟪x, fourierBasis i⟫_ℂ = fourierCoeff v (n - i) := by
    intro i
    rw [MeasureTheory.L2.inner_def]
    unfold fourierCoeff
    apply integral_congr_ae
    have hb : (⇑(fourierBasis (T := T) i)) =ᵐ[@haarAddCircle T hT]
        (fourier i : AddCircle T → ℂ) := by
      rw [coe_fourierBasis]
      exact ContinuousMap.coeFn_toLp (p := 2) (μ := @haarAddCircle T hT) (fourier i)
    filter_upwards [hx, hb] with t ht1 ht2
    rw [RCLike.inner_apply, ht1, ht2, smul_eq_mul, conj_fourier_mul,
      show -(n - i) = -n + i by ring, fourier_add]
    ring
  have h3 : ⟪x, u⟫_ℂ = fourierCoeff (fun t => (u : AddCircle T → ℂ) t *
      (v : AddCircle T → ℂ) t) n := by
    rw [MeasureTheory.L2.inner_def]
    unfold fourierCoeff
    apply integral_congr_ae
    filter_upwards [hx] with t ht
    rw [RCLike.inner_apply, ht, smul_eq_mul, conj_fourier_mul]
    ring
  simp only [h1, h2, h3] at hP
  convert hP using 1
  funext k
  ring

end NlsGge.Atomic.LIB006


/-! LIB-006 step 2(b)(i) (Mathlib-only): real weighted Cauchy-Schwarz for series, and the
l1 bound for a weighted-l2 nonnegative sequence: if `∑ (1+n²) β n² < ∞` then `β` is summable
and `(∑ β)² ≤ (∑ 1/(1+n²)) * ∑ (1+n²) β²`. -/

namespace NlsGge.Atomic.LIB006

open Filter

lemma summable_inv_one_add_sq : Summable (fun n : ℤ => 1 / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => 1 / (n : ℝ) ^ 2) ?_ ?_
  · exact Real.summable_one_div_int_pow.2 (by norm_num)
  · filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le hpos (by linarith)

lemma two_mul_le_weighted (w x : ℝ) (hw : 0 < w) :
    2 * x ≤ w * x ^ 2 + 1 / w := by
  have h1 : w * (1 / w) = 1 := by field_simp
  have hy : 0 < 1 / w := by positivity
  nlinarith [sq_nonneg (w * x - 1), mul_pos hw hy]

theorem summable_abs_of_weighted (β : ℤ → ℝ)
    (h : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * β n ^ 2)) :
    Summable (fun n : ℤ => |β n|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((h.add summable_inv_one_add_sq).div_const 2)
  have hw : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
  have := two_mul_le_weighted (1 + (n : ℝ) ^ 2) |β n| hw
  rw [sq_abs] at this
  linarith

/-- Weighted Cauchy-Schwarz for real series: `(∑ x y)² ≤ (∑ x) (∑ x y²)` for `x ≥ 0`. -/
theorem cs_tsum_real (x y : ℤ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hxs : Summable x) (hxy : Summable (fun k => x k * y k))
    (hxy2 : Summable (fun k => x k * y k ^ 2)) :
    (∑' k, x k * y k) ^ 2 ≤ (∑' k, x k) * ∑' k, x k * y k ^ 2 := by
  have hfin : ∀ s : Finset ℤ,
      (∑ k ∈ s, x k * y k) ^ 2 ≤ (∑ k ∈ s, x k) * ∑ k ∈ s, x k * y k ^ 2 := by
    intro s
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun k => x k * y k)
      (f := x) (g := fun k => x k * y k ^ 2) (fun k _ => hx k)
      (fun k _ => mul_nonneg (hx k) (sq_nonneg _)) ?_
    intro k _
    exact (by ring : (x k * y k) ^ 2 = x k * (x k * y k ^ 2)).le
  exact le_of_tendsto_of_tendsto' (Filter.Tendsto.pow hxy.hasSum 2)
    (Filter.Tendsto.mul hxs.hasSum hxy2.hasSum) hfin

/-- The l1 bound for a nonnegative weighted-l2 sequence. -/
theorem summable_and_sq_le_of_weighted (β : ℤ → ℝ) (hβ : ∀ k, 0 ≤ β k)
    (h : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * β n ^ 2)) :
    Summable β ∧
      (∑' k, β k) ^ 2 ≤
        (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * ∑' k : ℤ, (1 + (k : ℝ) ^ 2) * β k ^ 2 := by
  have hs : Summable β :=
    (summable_abs_of_weighted β h).congr (fun n => abs_of_nonneg (hβ n))
  have hw : ∀ k : ℤ, (1 + (k : ℝ) ^ 2) ≠ 0 := fun k => by positivity
  have hxy : Summable (fun k : ℤ => 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k)) :=
    hs.congr (fun k => by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ (hw k), one_mul])
  have hxy2 : Summable (fun k : ℤ => 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k) ^ 2) :=
    h.congr (fun k => by
      field_simp <;> ring)
  have hcs : (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k)) ^ 2 ≤
      (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
        ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k) ^ 2 :=
    cs_tsum_real (fun k : ℤ => 1 / (1 + (k : ℝ) ^ 2)) (fun k : ℤ => (1 + (k : ℝ) ^ 2) * β k)
      (fun k => by positivity) summable_inv_one_add_sq hxy hxy2
  have e1 : ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k) = ∑' k, β k :=
    tsum_congr (fun k => by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ (hw k), one_mul])
  have e2 : ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) * ((1 + (k : ℝ) ^ 2) * β k) ^ 2 =
      ∑' k : ℤ, (1 + (k : ℝ) ^ 2) * β k ^ 2 :=
    tsum_congr (fun k => by
      field_simp <;> ring)
  rw [e1, e2] at hcs
  exact ⟨hs, hcs⟩

/-- Shift invariance of the total mass of a summable real sequence. -/
theorem tsum_shift_sub (B : ℤ → ℝ) (n : ℤ) : ∑' k : ℤ, B (n - k) = ∑' k : ℤ, B k :=
  (Equiv.subLeft n).tsum_eq B

/-- Convolution with a summable sequence: each outer term is summable and the iterated sum
of `A2 k * B (n - k)` equals the product of the two masses. -/
theorem conv_summable_and_tsum (A2 B : ℤ → ℝ) (hA0 : ∀ k, 0 ≤ A2 k) (hB0 : ∀ k, 0 ≤ B k)
    (hB : Summable B) (hA : Summable A2) :
    Summable (fun n : ℤ => ∑' k : ℤ, A2 k * B (n - k)) ∧
      ∑' n : ℤ, ∑' k : ℤ, A2 k * B (n - k) = (∑' k, A2 k) * ∑' k, B k := by
  have hnonneg : ∀ p : ℤ × ℤ, 0 ≤ A2 p.1 * B (p.2 - p.1) :=
    fun p => mul_nonneg (hA0 _) (hB0 _)
  have hfib : ∀ k : ℤ, Summable (fun n : ℤ => A2 k * B (n - k)) := fun k =>
    ((Equiv.subRight k).summable_iff.mpr hB).mul_left (A2 k)
  have hinner : ∀ k : ℤ, ∑' n : ℤ, A2 k * B (n - k) = A2 k * ∑' n : ℤ, B n := fun k => by
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subRight k).tsum_eq B
  have hsum2 : Summable (fun k : ℤ => ∑' n : ℤ, A2 k * B (n - k)) :=
    (hA.mul_right (∑' n : ℤ, B n)).congr (fun k => (hinner k).symm)
  have hG : Summable (fun p : ℤ × ℤ => A2 p.1 * B (p.2 - p.1)) :=
    (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => A2 p.1 * B (p.2 - p.1)) hnonneg).mpr
      ⟨hfib, hsum2⟩
  have hF : Summable (Function.uncurry (fun n k : ℤ => A2 k * B (n - k))) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hG
  refine ⟨hF.prod, ?_⟩
  have hcomm : ∑' n : ℤ, ∑' k : ℤ, A2 k * B (n - k) =
      ∑' k : ℤ, ∑' n : ℤ, A2 k * B (n - k) := (Summable.tsum_comm hF).symm
  rw [hcomm]
  simp only [hinner]
  rw [tsum_mul_right]

/-- Young-type bound for the discrete convolution `ℓ² * ℓ¹ → ℓ²`, in squared form. -/
theorem young_sq_bound (A B : ℤ → ℝ) (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ k, 0 ≤ B k)
    (hB : Summable B) (hA2 : Summable (fun k => A k ^ 2)) :
    (∀ n : ℤ, Summable (fun k : ℤ => A k * B (n - k))) ∧
      Summable (fun n : ℤ => (∑' k : ℤ, A k * B (n - k)) ^ 2) ∧
      ∑' n : ℤ, (∑' k : ℤ, A k * B (n - k)) ^ 2 ≤ (∑' k, B k) ^ 2 * ∑' k : ℤ, A k ^ 2 := by
  have hBle : ∀ j : ℤ, B j ≤ ∑' k : ℤ, B k := fun j => hB.le_tsum j (fun i _ => hB0 i)
  have hB2 : Summable (fun j : ℤ => B j ^ 2) :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by nlinarith [hBle j, hB0 j]) (hB.mul_left (∑' k : ℤ, B k))
  have hBshift2 : ∀ n : ℤ, Summable (fun k : ℤ => B (n - k) ^ 2) := fun n =>
    (Equiv.subLeft n).summable_iff.mpr hB2
  have hBshift : ∀ n : ℤ, Summable (fun k : ℤ => B (n - k)) := fun n =>
    (Equiv.subLeft n).summable_iff.mpr hB
  have hsummand : ∀ n : ℤ, Summable (fun k : ℤ => A k * B (n - k)) := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hA0 k) (hB0 _))
      (fun k => by nlinarith [sq_nonneg (A k - B (n - k))])
      (((hA2).add (hBshift2 n)).div_const 2)
  have hpt : ∀ n : ℤ, (∑' k : ℤ, A k * B (n - k)) ^ 2 ≤
      (∑' k : ℤ, B k) * ∑' k : ℤ, A k ^ 2 * B (n - k) := by
    intro n
    have hxy : Summable (fun k : ℤ => B (n - k) * A k) :=
      (hsummand n).congr (fun k => mul_comm _ _)
    have hA2B : Summable (fun k : ℤ => A k ^ 2 * B (n - k)) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (hB0 _))
        (fun k => mul_le_mul_of_nonneg_left (hBle _) (sq_nonneg _))
        (hA2.mul_right (∑' k : ℤ, B k))
    have hxy2 : Summable (fun k : ℤ => B (n - k) * A k ^ 2) :=
      hA2B.congr (fun k => mul_comm _ _)
    have hcs : (∑' k : ℤ, B (n - k) * A k) ^ 2 ≤
        (∑' k : ℤ, B (n - k)) * ∑' k : ℤ, B (n - k) * A k ^ 2 :=
      cs_tsum_real (fun k : ℤ => B (n - k)) A (fun k => hB0 _) (hBshift n) hxy hxy2
    have e1 : ∑' k : ℤ, B (n - k) * A k = ∑' k : ℤ, A k * B (n - k) :=
      tsum_congr (fun k => mul_comm _ _)
    have e2 : ∑' k : ℤ, B (n - k) * A k ^ 2 = ∑' k : ℤ, A k ^ 2 * B (n - k) :=
      tsum_congr (fun k => mul_comm _ _)
    rw [e1, e2, tsum_shift_sub B n] at hcs
    exact hcs
  have hconv : Summable (fun n : ℤ => ∑' k : ℤ, A k ^ 2 * B (n - k)) ∧
      ∑' n : ℤ, ∑' k : ℤ, A k ^ 2 * B (n - k) = (∑' k, A k ^ 2) * ∑' k, B k :=
    conv_summable_and_tsum (fun k => A k ^ 2) B (fun k => sq_nonneg _) hB0 hB hA2
  have hF2 : Summable (fun n : ℤ => (∑' k : ℤ, A k * B (n - k)) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt (hconv.1.mul_left (∑' k : ℤ, B k))
  refine ⟨hsummand, hF2, ?_⟩
  calc ∑' n : ℤ, (∑' k : ℤ, A k * B (n - k)) ^ 2
      ≤ ∑' n : ℤ, (∑' k : ℤ, B k) * ∑' k : ℤ, A k ^ 2 * B (n - k) :=
        hF2.tsum_le_tsum hpt (hconv.1.mul_left (∑' k : ℤ, B k))
    _ = (∑' k : ℤ, B k) * ∑' n : ℤ, ∑' k : ℤ, A k ^ 2 * B (n - k) := tsum_mul_left
    _ = (∑' k : ℤ, B k) * ((∑' k, A k ^ 2) * ∑' k, B k) := by rw [hconv.2]
    _ = (∑' k : ℤ, B k) ^ 2 * ∑' k : ℤ, A k ^ 2 := by ring

/-- Square-summability of a nonnegative weighted-l2 sequence gives square-summability. -/
theorem sq_summable_of_weighted (α : ℤ → ℝ)
    (h : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * α n ^ 2)) :
    Summable (fun k : ℤ => α k ^ 2) :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => le_mul_of_one_le_left (sq_nonneg _) (by nlinarith [sq_nonneg (k : ℝ)])) h

/-- Product of two square-summable nonnegative sequences is summable. -/
theorem summable_mul_of_sq_summable (A B : ℤ → ℝ) (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ k, 0 ≤ B k)
    (hA2 : Summable (fun k => A k ^ 2)) (hB2 : Summable (fun k => B k ^ 2)) :
    Summable (fun k => A k * B k) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (hA0 k) (hB0 k))
    (fun k => by nlinarith [sq_nonneg (A k - B k)]) ((hA2.add hB2).div_const 2)

/-- Reflection of a convolution: the two orders of the convolution agree. -/
theorem conv_flip (f g : ℤ → ℝ) (n : ℤ) :
    ∑' k : ℤ, f k * g (n - k) = ∑' k : ℤ, g k * f (n - k) := by
  have h := (Equiv.subLeft n).tsum_eq (fun k => f k * g (n - k))
  simp only [Equiv.subLeft_apply, sub_sub_cancel] at h
  rw [← h]
  exact tsum_congr (fun k => by ring)

/-- The weight splitting `√(1+n²) ≤ √2 (√(1+k²) + √(1+(n-k)²))`. -/
theorem sqrt_weight_split (n k : ℤ) :
    Real.sqrt (1 + (n : ℝ) ^ 2) ≤
      Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) + Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2)) := by
  have hcast : ((n - k : ℤ) : ℝ) = (n : ℝ) - (k : ℝ) := by push_cast; ring
  have hx : (0 : ℝ) ≤ Real.sqrt (1 + (k : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hy : (0 : ℝ) ≤ Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) := Real.sqrt_nonneg _
  have hx2 : Real.sqrt (1 + (k : ℝ) ^ 2) ^ 2 = 1 + (k : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have hy2 : Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) ^ 2 = 1 + ((n - k : ℤ) : ℝ) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hm : ((n - k : ℤ) : ℝ) ^ 2 = ((n : ℝ) - k) ^ 2 := by rw [hcast]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have key : (Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) +
      Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2))) ^ 2 =
      2 * (Real.sqrt (1 + (k : ℝ) ^ 2) ^ 2 + Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) ^ 2 +
        2 * (Real.sqrt (1 + (k : ℝ) ^ 2) * Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2))) := by
    rw [mul_pow, h22]; ring
  rw [key, hx2, hy2]
  nlinarith [sq_nonneg ((n : ℝ) - 2 * k), mul_nonneg hx hy, hm]

/-- Squared form of the splitting inequality. -/
theorem sq_le_four_split (y F G : ℝ) (hy : 0 ≤ y) (h : y ≤ Real.sqrt 2 * (F + G)) :
    y ^ 2 ≤ 4 * (F ^ 2 + G ^ 2) := by
  have hsq := sq_le_sq' (by linarith) h
  have e2 : (Real.sqrt 2 * (F + G)) ^ 2 = 2 * (F + G) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [e2] at hsq
  nlinarith [sq_nonneg (F - G)]

/-- Pointwise bound of `√(1+n²) * ∑_k α_k β_{n-k}` by the two convolutions. -/
theorem conv_pointwise_bound (α β : ℤ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα2 : Summable (fun k : ℤ => α k ^ 2))
    (hD2 : Summable (fun k : ℤ => (Real.sqrt (1 + (k : ℝ) ^ 2) * β k) ^ 2))
    (hT : ∀ n : ℤ, Summable (fun k : ℤ => α k * β (n - k)))
    (hF : ∀ n : ℤ, Summable (fun k : ℤ => Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k)))
    (n : ℤ) :
    Real.sqrt (1 + (n : ℝ) ^ 2) * ∑' k : ℤ, α k * β (n - k) ≤
      Real.sqrt 2 * ((∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k)) +
        ∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * β k * α (n - k)) := by
  have hD2n : Summable (fun k : ℤ => (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k)) ^ 2) :=
    (Equiv.subLeft n).summable_iff.mpr hD2
  have hs2 : Summable (fun k : ℤ => α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))) :=
    summable_mul_of_sq_summable α (fun k => Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))
      hα0 (fun k => mul_nonneg (Real.sqrt_nonneg _) (hβ0 _)) hα2 hD2n
  have hflip : ∑' k : ℤ, α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k)) =
      ∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * β k * α (n - k) :=
    conv_flip α (fun j : ℤ => Real.sqrt (1 + (j : ℝ) ^ 2) * β j) n
  have hsplit : ∀ k : ℤ, Real.sqrt (1 + (n : ℝ) ^ 2) * (α k * β (n - k)) ≤
      Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k) +
        α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))) := by
    intro k
    have hab : 0 ≤ α k * β (n - k) := mul_nonneg (hα0 k) (hβ0 _)
    calc Real.sqrt (1 + (n : ℝ) ^ 2) * (α k * β (n - k))
        ≤ Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) + Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2)) *
            (α k * β (n - k)) := mul_le_mul_of_nonneg_right (sqrt_weight_split n k) hab
      _ = Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k) +
            α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))) := by ring
  calc Real.sqrt (1 + (n : ℝ) ^ 2) * ∑' k : ℤ, α k * β (n - k)
      = ∑' k : ℤ, Real.sqrt (1 + (n : ℝ) ^ 2) * (α k * β (n - k)) := tsum_mul_left.symm
    _ ≤ ∑' k : ℤ, Real.sqrt 2 * (Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k) +
          α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))) :=
        Summable.tsum_le_tsum hsplit ((hT n).mul_left _) (((hF n).add hs2).mul_left _)
    _ = Real.sqrt 2 * ((∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k)) +
          ∑' k : ℤ, α k * (Real.sqrt (1 + ((n - k : ℤ) : ℝ) ^ 2) * β (n - k))) := by
        rw [tsum_mul_left, Summable.tsum_add (hF n) hs2]
    _ = Real.sqrt 2 * ((∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k)) +
          ∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * β k * α (n - k)) := by
        rw [hflip]

/-- Squared weighted summation from the pointwise splitting bound. -/
theorem house_sq_sum (F G γ T : ℤ → ℝ) (hγ0 : ∀ n : ℤ, 0 ≤ γ n) (hγT : ∀ n : ℤ, γ n ≤ T n)
    (hT : ∀ n : ℤ, Real.sqrt (1 + (n : ℝ) ^ 2) * T n ≤ Real.sqrt 2 * (F n + G n))
    (hF : Summable (fun n => F n ^ 2)) (hG : Summable (fun n => G n ^ 2)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * γ n ^ 2) ∧
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * γ n ^ 2 ≤ 4 * (∑' n, F n ^ 2 + ∑' n, G n ^ 2) := by
  have hpt : ∀ n : ℤ, (1 + (n : ℝ) ^ 2) * γ n ^ 2 ≤ 4 * (F n ^ 2 + G n ^ 2) := by
    intro n
    have hx0 : 0 ≤ Real.sqrt (1 + (n : ℝ) ^ 2) * γ n :=
      mul_nonneg (Real.sqrt_nonneg _) (hγ0 n)
    have hx1 : Real.sqrt (1 + (n : ℝ) ^ 2) * γ n ≤ Real.sqrt (1 + (n : ℝ) ^ 2) * T n :=
      mul_le_mul_of_nonneg_left (hγT n) (Real.sqrt_nonneg _)
    have h := sq_le_four_split _ (F n) (G n) hx0 (le_trans hx1 (hT n))
    have e1 : (Real.sqrt (1 + (n : ℝ) ^ 2) * γ n) ^ 2 = (1 + (n : ℝ) ^ 2) * γ n ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [e1] at h
    exact h
  have hP : Summable (fun n : ℤ => 4 * (F n ^ 2 + G n ^ 2)) := (hF.add hG).mul_left 4
  have hγs : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * γ n ^ 2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (sq_nonneg _)) hpt hP
  refine ⟨hγs, ?_⟩
  calc ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * γ n ^ 2 ≤ ∑' n : ℤ, 4 * (F n ^ 2 + G n ^ 2) :=
        Summable.tsum_le_tsum hpt hγs hP
    _ = 4 * (∑' n, F n ^ 2 + ∑' n, G n ^ 2) := by
        rw [tsum_mul_left, Summable.tsum_add hF hG]

/-- Real-level discrete Young estimate for the weighted product `√(1+n²) γ_n`, with
`γ_n ≤ ∑ α_k β_{n-k}`. -/
theorem house_mul_bound_real (α β γ : ℤ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hWα : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * α n ^ 2))
    (hWβ : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * β n ^ 2))
    (hγ0 : ∀ n, 0 ≤ γ n) (hγ : ∀ n, γ n ≤ ∑' k : ℤ, α k * β (n - k)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * γ n ^ 2) ∧
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * γ n ^ 2 ≤
        (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) *
            (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2) := by
  obtain ⟨hαs, hαsq⟩ := summable_and_sq_le_of_weighted α hα0 hWα
  obtain ⟨hβs, hβsq⟩ := summable_and_sq_le_of_weighted β hβ0 hWβ
  have hα2 : Summable (fun k : ℤ => α k ^ 2) := sq_summable_of_weighted α hWα
  have hwpos : ∀ k : ℤ, 0 ≤ Real.sqrt (1 + (k : ℝ) ^ 2) := fun k => Real.sqrt_nonneg _
  have hA0 : ∀ k : ℤ, 0 ≤ Real.sqrt (1 + (k : ℝ) ^ 2) * α k :=
    fun k => mul_nonneg (hwpos k) (hα0 k)
  have hD0 : ∀ k : ℤ, 0 ≤ Real.sqrt (1 + (k : ℝ) ^ 2) * β k :=
    fun k => mul_nonneg (hwpos k) (hβ0 k)
  have hA2 : Summable (fun k : ℤ => (Real.sqrt (1 + (k : ℝ) ^ 2) * α k) ^ 2) :=
    hWα.congr (fun k => by rw [mul_pow, Real.sq_sqrt (by positivity)])
  have hD2 : Summable (fun k : ℤ => (Real.sqrt (1 + (k : ℝ) ^ 2) * β k) ^ 2) :=
    hWβ.congr (fun k => by rw [mul_pow, Real.sq_sqrt (by positivity)])
  have hAsum : ∑' k : ℤ, (Real.sqrt (1 + (k : ℝ) ^ 2) * α k) ^ 2 =
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2 :=
    tsum_congr (fun k => by rw [mul_pow, Real.sq_sqrt (by positivity)])
  have hDsum : ∑' k : ℤ, (Real.sqrt (1 + (k : ℝ) ^ 2) * β k) ^ 2 =
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2 :=
    tsum_congr (fun k => by rw [mul_pow, Real.sq_sqrt (by positivity)])
  obtain ⟨hT1s, -, -⟩ := young_sq_bound α β hα0 hβ0 hβs hα2
  obtain ⟨hF1s, hF1sq, hF1bd⟩ :=
    young_sq_bound (fun k => Real.sqrt (1 + (k : ℝ) ^ 2) * α k) β hA0 hβ0 hβs hA2
  obtain ⟨hG1s, hG1sq, hG1bd⟩ :=
    young_sq_bound (fun k => Real.sqrt (1 + (k : ℝ) ^ 2) * β k) α hD0 hα0 hαs hD2
  beta_reduce at hF1s hF1sq hF1bd hG1s hG1sq hG1bd
  rw [hAsum] at hF1bd
  rw [hDsum] at hG1bd
  obtain ⟨hγs, hγbd⟩ := house_sq_sum
    (fun n => ∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k))
    (fun n => ∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * β k * α (n - k)) γ
    (fun n => ∑' k : ℤ, α k * β (n - k)) hγ0 hγ
    (fun n : ℤ => conv_pointwise_bound α β hα0 hβ0 hα2 hD2 hT1s hF1s n) hF1sq hG1sq
  have i1 : (∑' k : ℤ, β k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) ≤
      (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2) *
        (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) :=
    mul_le_mul_of_nonneg_right hβsq (tsum_nonneg (fun n => mul_nonneg (by positivity) (sq_nonneg _)))
  have i2 : (∑' k : ℤ, α k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2) ≤
      (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) *
        (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2) :=
    mul_le_mul_of_nonneg_right hαsq (tsum_nonneg (fun n => mul_nonneg (by positivity) (sq_nonneg _)))
  refine ⟨hγs, le_trans hγbd ?_⟩
  have hb1 : 4 * ((∑' n : ℤ, (∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * α k * β (n - k)) ^ 2) +
      ∑' n : ℤ, (∑' k : ℤ, Real.sqrt (1 + (k : ℝ) ^ 2) * β k * α (n - k)) ^ 2) ≤
      4 * ((∑' k : ℤ, β k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) +
        (∑' k : ℤ, α k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2)) :=
    mul_le_mul_of_nonneg_left (add_le_add hF1bd hG1bd) (by norm_num)
  have hb2 : 4 * ((∑' k : ℤ, β k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) +
        (∑' k : ℤ, α k) ^ 2 * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2)) ≤
      4 * ((∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2) *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) +
        (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * α n ^ 2) *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * β n ^ 2)) :=
    mul_le_mul_of_nonneg_left (add_le_add i1 i2) (by norm_num)
  linarith [hb1, hb2]

end NlsGge.Atomic.LIB006

namespace NlsGge.Atomic.LIB006
open Filter

/-- Complex-level weighted product estimate for Fourier convolutions. -/
theorem house_mul_bound (a b c : ℤ → ℂ)
    (ha : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2))
    (hb : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖b n‖ ^ 2))
    (hc : ∀ n : ℤ, HasSum (fun k : ℤ => a k * b (n - k)) (c n)) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖c n‖ ^ 2) ∧
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖c n‖ ^ 2 ≤
        (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2) *
            (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖b n‖ ^ 2) := by
  have hα2 : Summable (fun k : ℤ => ‖a k‖ ^ 2) := sq_summable_of_weighted (fun k => ‖a k‖) ha
  have hbℓ1 : Summable (fun k : ℤ => ‖b k‖) :=
    (summable_and_sq_le_of_weighted (fun k => ‖b k‖) (fun k => norm_nonneg _) hb).1
  have hsumn : ∀ n : ℤ, Summable (fun k : ℤ => ‖a k‖ * ‖b (n - k)‖) := fun n =>
    (young_sq_bound (fun k => ‖a k‖) (fun k => ‖b k‖) (fun k => norm_nonneg _)
      (fun k => norm_nonneg _) hbℓ1 hα2).1 n
  have hcn : ∀ n : ℤ, ‖c n‖ ≤ ∑' k : ℤ, ‖a k‖ * ‖b (n - k)‖ := fun n => by
    rw [← (hc n).tsum_eq]
    calc ‖∑' k : ℤ, a k * b (n - k)‖ ≤ ∑' k : ℤ, ‖a k * b (n - k)‖ :=
          norm_tsum_le_tsum_norm (by simpa only [norm_mul] using hsumn n)
      _ = ∑' k : ℤ, ‖a k‖ * ‖b (n - k)‖ := tsum_congr (fun k => norm_mul _ _)
  exact house_mul_bound_real (fun k => ‖a k‖) (fun k => ‖b k‖) (fun n => ‖c n‖)
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) ha hb (fun n => norm_nonneg _) hcn


end NlsGge.Atomic.LIB006

/-! ## LIB-006 bridge to the production physical L2 carrier (steps 2(c), 2(d), 3-5). -/

namespace NlsGge.Atomic.LIB005

open NlsGge.Pilot NlsGge.Analysis

/-- Continuous-field multiplier on the physical L2 class. Verbatim from the Pro design
(DEFINITIONS/LIB.lean.md, the `h1MulL2` block of the LIB-005/006/087 section), applied to the
existing `physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites` and
`physicalH1Continuous`. -/
noncomputable def h1MulL2 (a : PhysicalL2)
    (ha : SobolevSquareSummable 1 (physicalFourier a)) :
    PhysicalL2 →L[ℂ] PhysicalL2 :=
  physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites
    (physicalH1Continuous a ha)

end NlsGge.Atomic.LIB005

namespace NlsGge.Atomic.LIB006

open MeasureTheory NlsGge.Pilot NlsGge.Analysis NlsGge.Atomic.LIB002 NlsGge.Atomic.LIB004
open NlsGge.Atomic.LIB005
open scoped ENNReal ComplexConjugate

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem sobolev_one_iff' (x : ℤ → ℂ) :
    SobolevSquareSummable 1 x ↔ Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2) := by
  unfold SobolevSquareSummable
  simp only [japaneseBracket_h1_weight]

theorem h1MulL2_coe_ae (a : PhysicalL2) (ha : SobolevSquareSummable 1 (physicalFourier a))
    (f : PhysicalL2) :
    ((h1MulL2 a ha f : PhysicalL2) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun x => (a : PhysicalCircle → ℂ) x * (f : PhysicalCircle → ℂ) x := by
  have hcont : (physicalH1Continuous a ha : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      (a : PhysicalCircle → ℂ) := by
    have h : (ContinuousMap.toLp (2 : ℝ≥0∞) spatialMeasure ℂ (physicalH1Continuous a ha) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (physicalH1Continuous a ha : PhysicalCircle → ℂ) :=
      ContinuousMap.coeFn_toLp _ _
    rw [physicalH1Continuous_toLp a ha] at h
    exact h.symm
  have hm : ((h1MulL2 a ha f : PhysicalL2) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun x => (ContinuousMap.toLp (∞ : ℝ≥0∞) spatialMeasure ℂ
        (physicalH1Continuous a ha) : PhysicalCircle → ℂ) x * (f : PhysicalCircle → ℂ) x :=
    (ContinuousLinearMap.mul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).coeFn_holder (r := (2 : ℝ≥0∞))
      (ContinuousMap.toLp (∞ : ℝ≥0∞) spatialMeasure ℂ (physicalH1Continuous a ha)) f
  have hinf : (ContinuousMap.toLp (∞ : ℝ≥0∞) spatialMeasure ℂ (physicalH1Continuous a ha) :
      PhysicalCircle → ℂ) =ᵐ[spatialMeasure] (physicalH1Continuous a ha : PhysicalCircle → ℂ) :=
    ContinuousMap.coeFn_toLp _ _
  filter_upwards [hm, hinf, hcont] with x h1 h2 h3
  rw [h1, h2, h3]

theorem physicalFourier_add (x y : PhysicalL2) (n : ℤ) :
    physicalFourier ((x + y : PhysicalL2) : PhysicalCircle → ℂ) n =
      physicalFourier x n + physicalFourier y n := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, ← physicalFourierL2_apply, map_add]
  rfl

theorem h1MulL2_fourier_hasSum (u v : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    HasSum (fun k : ℤ => physicalFourier u k * physicalFourier v (n - k))
      (physicalFourier (h1MulL2 u hu v) n) := by
  have heq : physicalFourier (h1MulL2 u hu v) n =
      fourierCoeff (fun t => (u : PhysicalCircle → ℂ) t * (v : PhysicalCircle → ℂ) t) n := by
    unfold physicalFourier fourierCoeff
    apply integral_congr_ae
    filter_upwards [h1MulL2_coe_ae u hu v] with x hx
    rw [hx]
  rw [heq]
  exact fourierCoeff_mul_hasSum (T := 1) u v n

theorem fourierMultiplier_one_add (k m : ℤ) :
    NlsGge.Atomic.LIB002.fourierMultiplier 1 (k + m) = NlsGge.Atomic.LIB002.fourierMultiplier 1 k + NlsGge.Atomic.LIB002.fourierMultiplier 1 m := by
  unfold NlsGge.Atomic.LIB002.fourierMultiplier
  push_cast
  ring

theorem fourierMultiplier_one_eq_mul_I (n : ℤ) :
    NlsGge.Atomic.LIB002.fourierMultiplier 1 n = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
  unfold NlsGge.Atomic.LIB002.fourierMultiplier
  push_cast
  ring

theorem conj_fourierMultiplier_one_neg (n : ℤ) :
    conj (NlsGge.Atomic.LIB002.fourierMultiplier 1 (-n)) = NlsGge.Atomic.LIB002.fourierMultiplier 1 n := by
  rw [fourierMultiplier_one_eq_mul_I, fourierMultiplier_one_eq_mul_I, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem product_coeff_identity (u v du dv : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v))
    (hdu : HasWeakDerivativeL2 1 1 u du) (hdv : HasWeakDerivativeL2 1 1 v dv) (n : ℤ) :
    physicalFourier ((h1MulL2 v hv du + h1MulL2 u hu dv : PhysicalL2) : PhysicalCircle → ℂ) n =
      NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier (h1MulL2 u hu v) n := by
  have hdu_c : ∀ k : ℤ, physicalFourier du k = NlsGge.Atomic.LIB002.fourierMultiplier 1 k ^ 1 * physicalFourier u k :=
    fun k => weakDerivative_fourierCoeff hdu k
  have hdv_c : ∀ k : ℤ, physicalFourier dv k = NlsGge.Atomic.LIB002.fourierMultiplier 1 k ^ 1 * physicalFourier v k :=
    fun k => weakDerivative_fourierCoeff hdv k
  have T0 := h1MulL2_fourier_hasSum u v hu n
  have T1 := h1MulL2_fourier_hasSum v du hv n
  have T2 := h1MulL2_fourier_hasSum u dv hu n
  have T1' : HasSum (fun k : ℤ => physicalFourier du k * physicalFourier v (n - k))
      (physicalFourier (h1MulL2 v hv du) n) := by
    have h := (Equiv.subLeft n).hasSum_iff.mpr T1
    have hfun : ((fun k : ℤ => physicalFourier v k * physicalFourier du (n - k)) ∘
        (Equiv.subLeft n)) = fun k : ℤ => physicalFourier du k * physicalFourier v (n - k) := by
      funext k
      simp only [Function.comp, Equiv.subLeft_apply, sub_sub_cancel]
      ring
    rw [hfun] at h
    exact h
  have H := T1'.add T2
  have hterm : (fun k : ℤ => physicalFourier du k * physicalFourier v (n - k) +
      physicalFourier u k * physicalFourier dv (n - k)) =
      fun k : ℤ => NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * (physicalFourier u k * physicalFourier v (n - k)) := by
    funext k
    have hM : NlsGge.Atomic.LIB002.fourierMultiplier 1 n = NlsGge.Atomic.LIB002.fourierMultiplier 1 k + NlsGge.Atomic.LIB002.fourierMultiplier 1 (n - k) := by
      have h := fourierMultiplier_one_add k (n - k)
      rw [show k + (n - k) = n by ring] at h
      exact h
    rw [hdu_c k, hdv_c (n - k), hM]
    ring
  rw [hterm] at H
  have H2 := T0.mul_left (NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1)
  rw [physicalFourier_add]
  exact H.unique H2

theorem product_hasWeak (u v du dv : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v))
    (hdu : HasWeakDerivativeL2 1 1 u du) (hdv : HasWeakDerivativeL2 1 1 v dv) :
    HasWeakDerivativeL2 1 1 (h1MulL2 u hu v) (h1MulL2 v hv du + h1MulL2 u hu dv) := by
  refine (weakDerivative_fourierCoeff_iff (T := 1)).mpr ?_
  intro n
  exact product_coeff_identity u v du dv hu hv hdu hdv n

theorem product_graph_bound (u v : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    SobolevSquareSummable 1 (physicalFourier (h1MulL2 u hu v)) ∧
      h1GraphNorm (h1MulL2 u hu v) ≤
        (2 * Real.pi * Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2))) *
          h1GraphNorm u * h1GraphNorm v := by
  obtain ⟨hs, hbd⟩ := house_mul_bound (fun k => physicalFourier u k)
    (fun k => physicalFourier v k) (fun n => physicalFourier (h1MulL2 u hu v) n)
    ((sobolev_one_iff' _).mp hu) ((sobolev_one_iff' _).mp hv)
    (fun n => h1MulL2_fourier_hasSum u v hu n)
  have hp : SobolevSquareSummable 1 (physicalFourier (h1MulL2 u hu v)) :=
    (sobolev_one_iff' _).mpr hs
  have hS0 : 0 ≤ ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2) :=
    tsum_nonneg (fun k => by positivity)
  have hpn := house_norm_sq (h1MulL2 u hu v) hp
  have hun := house_norm_sq u hu
  have hvn := house_norm_sq v hv
  have hb1 := (h1GraphNorm_house_bounds _ hp).2
  have hu1 := (h1GraphNorm_house_bounds u hu).1
  have hv1 := (h1GraphNorm_house_bounds v hv).1
  have h2 : ‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖ ^ 2 ≤
      8 * (∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * ‖physicalSobolevL2 1 u hu‖ ^ 2 *
        ‖physicalSobolevL2 1 v hv‖ ^ 2 := by
    rw [hpn, hun, hvn]
    exact hbd
  have hnorm : ‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖ ≤
      Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * ‖physicalSobolevL2 1 u hu‖ *
        ‖physicalSobolevL2 1 v hv‖ := by
    have hy : 0 ≤ Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * ‖physicalSobolevL2 1 u hu‖ *
        ‖physicalSobolevL2 1 v hv‖ := by positivity
    have hsq : ‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖ ^ 2 ≤
        (Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) * ‖physicalSobolevL2 1 u hu‖ *
          ‖physicalSobolevL2 1 v hv‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
      linarith [h2]
    calc ‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖
        = Real.sqrt (‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u hu‖ * ‖physicalSobolevL2 1 v hv‖) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_sq hy
  have hK : 0 ≤ 2 * Real.pi := by positivity
  have hprod : ‖physicalSobolevL2 1 u hu‖ * ‖physicalSobolevL2 1 v hv‖ ≤
      h1GraphNorm u * h1GraphNorm v :=
    mul_le_mul hu1 hv1 (norm_nonneg _) (le_trans (norm_nonneg _) hu1)
  refine ⟨hp, ?_⟩
  calc h1GraphNorm (h1MulL2 u hu v)
      ≤ 2 * Real.pi * ‖physicalSobolevL2 1 (h1MulL2 u hu v) hp‖ := hb1
    _ ≤ 2 * Real.pi * (Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          ‖physicalSobolevL2 1 u hu‖ * ‖physicalSobolevL2 1 v hv‖) :=
        mul_le_mul_of_nonneg_left hnorm hK
    _ ≤ 2 * Real.pi * (Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
          (h1GraphNorm u * h1GraphNorm v)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        calc Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
              ‖physicalSobolevL2 1 u hu‖ * ‖physicalSobolevL2 1 v hv‖
            = Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
                (‖physicalSobolevL2 1 u hu‖ * ‖physicalSobolevL2 1 v hv‖) := by ring
          _ ≤ Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) *
                (h1GraphNorm u * h1GraphNorm v) :=
              mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)
    _ = (2 * Real.pi * Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2))) *
          h1GraphNorm u * h1GraphNorm v := by ring

theorem exists_star_ae (u : PhysicalL2) :
    ∃ w : PhysicalL2, (w : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun t => star ((u : PhysicalCircle → ℂ) t) := by
  have hu : MemLp (fun t => (u : PhysicalCircle → ℂ) t) 2 spatialMeasure := Lp.memLp u
  have hmeas : AEStronglyMeasurable (fun t => star ((u : PhysicalCircle → ℂ) t)) spatialMeasure :=
    hu.aestronglyMeasurable.star
  have hmem : MemLp (fun t => star ((u : PhysicalCircle → ℂ) t)) 2 spatialMeasure :=
    MemLp.of_le hu.norm hmeas (ae_of_all _ fun t => by rw [norm_star, norm_norm])
  exact ⟨hmem.toLp _, hmem.coeFn_toLp⟩

theorem physicalFourier_star_ae (w f : PhysicalL2)
    (h : (w : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun t => star ((f : PhysicalCircle → ℂ) t))
    (n : ℤ) : physicalFourier w n = conj (physicalFourier f (-n)) := by
  unfold physicalFourier fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [h] with t ht
  rw [ht, smul_eq_mul, smul_eq_mul, neg_neg, map_mul, fourier_neg]
  rfl

theorem conj_hasWeak (u du cu cdu : PhysicalL2)
    (hdu : HasWeakDerivativeL2 1 1 u du)
    (hcu : (cu : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun t => star ((u : PhysicalCircle → ℂ) t))
    (hcdu : (cdu : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun t => star ((du : PhysicalCircle → ℂ) t)) :
    HasWeakDerivativeL2 1 1 cu cdu := by
  refine (weakDerivative_fourierCoeff_iff (T := 1)).mpr ?_
  intro n
  show physicalFourier cdu n = NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier cu n
  have hd : physicalFourier du (-n) = NlsGge.Atomic.LIB002.fourierMultiplier 1 (-n) ^ 1 * physicalFourier u (-n) :=
    weakDerivative_fourierCoeff hdu (-n)
  rw [physicalFourier_star_ae cdu du hcdu n, physicalFourier_star_ae cu u hcu n, hd, map_mul,
    map_pow, conj_fourierMultiplier_one_neg]

/-- LIB-006 (Pro signature, verbatim). -/
theorem h1_mul_weakDeriv :
  ∃ C : ℝ, 0 < C ∧ ∀ (u v : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v)),
    SobolevSquareSummable 1 (physicalFourier (h1MulL2 u hu v)) ∧
    h1GraphNorm (h1MulL2 u hu v) ≤ C * h1GraphNorm u * h1GraphNorm v ∧
    ∃ du dv q dq : PhysicalL2,
      HasWeakDerivativeL2 1 1 u du ∧ HasWeakDerivativeL2 1 1 v dv ∧
      HasWeakDerivativeL2 1 1 (h1MulL2 u hu v)
        (h1MulL2 v hv du + h1MulL2 u hu dv) ∧
      SobolevSquareSummable 1 (physicalFourier q) ∧
      HasWeakDerivativeL2 1 1 q dq ∧
      ((q : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
        fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) ∧
      ((dq : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
        fun x => ((2 * (star (u x) * du x).re : ℝ) : ℂ)) := by
  have hn : ∀ w : PhysicalL2, 0 ≤ h1GraphNorm w := fun w => Real.sqrt_nonneg _
  refine ⟨2 * Real.pi * Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) + 1, by positivity, ?_⟩
  intro u v hu hv
  obtain ⟨hp, hbd⟩ := product_graph_bound u v hu hv
  refine ⟨hp, ?_, ?_⟩
  · have key : (2 * Real.pi * Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2))) * h1GraphNorm u ≤
        (2 * Real.pi * Real.sqrt (8 * ∑' k : ℤ, 1 / (1 + (k : ℝ) ^ 2)) + 1) * h1GraphNorm u :=
      mul_le_mul_of_nonneg_right (by linarith) (hn u)
    exact le_trans hbd (mul_le_mul_of_nonneg_right key (hn v))
  · obtain ⟨du, hdu⟩ := (h1_iff_weak_derivative u).mp hu
    obtain ⟨dv, hdv⟩ := (h1_iff_weak_derivative v).mp hv
    obtain ⟨cu, hcu⟩ := exists_star_ae u
    obtain ⟨cdu, hcdu⟩ := exists_star_ae du
    have hcudu : HasWeakDerivativeL2 1 1 cu cdu := conj_hasWeak u du cu cdu hdu hcu hcdu
    have hcuH : SobolevSquareSummable 1 (physicalFourier cu) :=
      (h1_iff_weak_derivative cu).mpr ⟨cdu, hcudu⟩
    obtain ⟨hqp, -⟩ := product_graph_bound cu u hcuH hu
    refine ⟨du, dv, h1MulL2 cu hcuH u, h1MulL2 u hu cdu + h1MulL2 cu hcuH du, hdu, hdv,
      product_hasWeak u v du dv hu hv hdu hdv, hqp,
      product_hasWeak cu u cdu du hcuH hu hcudu hdu, ?_, ?_⟩
    · filter_upwards [h1MulL2_coe_ae cu hcuH u, hcu] with x hx1 hx2
      rw [hx1, hx2]
      push_cast
      exact Complex.conj_mul' (u x)
    · filter_upwards [Lp.coeFn_add (h1MulL2 u hu cdu) (h1MulL2 cu hcuH du),
        h1MulL2_coe_ae u hu cdu, h1MulL2_coe_ae cu hcuH du, hcdu, hcu] with x a1 a2 a3 a4 a5
      rw [a1, Pi.add_apply, a2, a3, a4, a5]
      rw [show ((2 * (star (u x) * du x).re : ℝ) : ℂ) =
          (star (u x) * du x) + conj (star (u x) * du x) from (Complex.add_conj _).symm]
      simp only [Complex.star_def, map_mul, Complex.conj_conj]
      ring

end NlsGge.Atomic.LIB006
