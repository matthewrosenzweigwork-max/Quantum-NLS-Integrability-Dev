import Mathlib
import NlsGge.Atomic.G1.G1104Host
import NlsGge.Atomic.G1.G1104Sup
import NlsGge.Atomic.G1.G1104ODE
import NlsGge.Atomic.G1.G1104FD
import NlsGge.Atomic.G1.G1104Ker
import NlsGge.Atomic.G1.G1104Jor
import NlsGge.ThirdConsultation.G1.G1104SNF

/-!
# G1-104 M5: concrete Smith continuation and jet count

Concrete M5 for the actual characteristic matrix of the ZS realization.
Taylor matrix `charTaylorMatrix` (entries are the M4 coefficients `tayD`); then

* `dvd_of_order_le`: valuation divisibility in `ℂ⟦X⟧`;
* `smith_two`: a 2 x 2 matrix over `ℂ⟦X⟧` with nonzero determinant has a diagonal Smith form
  `U M V = diag(p, q)` (`U`, `V` with unit determinant, `p`, `q` nonzero; no divisibility
  `p ∣ q` is needed or claimed, both orders may be positive);
* `HasPSAt` calculus: absolutely convergent power-series product/difference and the identity of
  the formal order with `analyticOrderAt`;
* truncated jets `JQ N = ℂ⟦X⟧ / (X^N)`: dimension of the kernel of multiplication by a
  nonzero series is `min N (order)`;
* `charTaylorMatrix_det_ne_zero`, `exists_smith_factorization_charTaylorMatrix`,
  `tayKer_finrank_eq_detOrder`, `charTaylorMatrix_det_order_eq_analyticOrderAt`,
  `concrete_tayKer_finrank_eq_analyticOrderAt`.
-/

set_option autoImplicit false

open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB033
open NlsGge.GK38
open NlsGge.Atomic.G1104Jor NlsGge.Atomic.G1104ODE NlsGge.Atomic.G1104Ker
open NlsGge.GKDefinitionDesign NlsGge.Atomic.LIB038
open NlsGge.ThirdConsultation.G1.G1104SNF

noncomputable section

namespace NlsGge.ThirdConsultation.G1.G1104SNF3

section PowerSeriesAlgebra
open PowerSeries

theorem dvd_of_order_le {a b : PowerSeries ℂ} (ha : a ≠ 0)
    (h : PowerSeries.order a ≤ PowerSeries.order b) : a ∣ b := by
  by_cases hb : b = 0
  · exact ⟨0, by simp [hb]⟩
  have hm : (a.order.toNat : ℕ∞) = a.order := PowerSeries.coe_toNat_order ha
  have hn : (b.order.toNat : ℕ∞) = b.order := PowerSeries.coe_toNat_order hb
  have hmn : a.order.toNat ≤ b.order.toNat := by
    have : (a.order.toNat : ℕ∞) ≤ (b.order.toNat : ℕ∞) := by rw [hm, hn]; exact h
    exact_mod_cast this
  have hXb : (X : PowerSeries ℂ) ^ a.order.toNat ∣ b :=
    (pow_dvd_pow X hmn).trans PowerSeries.X_pow_order_dvd
  obtain ⟨t, ht⟩ := hXb
  have hu : IsUnit (PowerSeries.divXPowOrder a) := PowerSeries.isUnit_divided_by_X_pow_order ha
  obtain ⟨v, hv⟩ := hu
  have hfa : (X : PowerSeries ℂ) ^ a.order.toNat * PowerSeries.divXPowOrder a = a :=
    PowerSeries.X_pow_order_mul_divXPowOrder
  refine ⟨(↑v⁻¹ : PowerSeries ℂ) * t, ?_⟩
  calc b = X ^ a.order.toNat * t := ht
    _ = (X ^ a.order.toNat * (v : PowerSeries ℂ)) * ((↑v⁻¹ : PowerSeries ℂ) * t) := by
        rw [← mul_assoc, mul_assoc (X ^ a.order.toNat), Units.mul_inv, mul_one]
    _ = a * ((↑v⁻¹ : PowerSeries ℂ) * t) := by rw [hv, hfa]


/-! ### Smith factorization of a 2×2 matrix over `ℂ⟦X⟧` -/

/-- Swap matrix. -/
def Sw : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) := !![0, 1; 1, 0]

theorem smith_core (M : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (ha : M 0 0 ≠ 0) (hb : M 0 0 ∣ M 0 1) (hc : M 0 0 ∣ M 1 0) (hdet : M.det ≠ 0) :
    ∃ (U V : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (p q : PowerSeries ℂ),
      U * M * V = diagonalTwo p q ∧ IsUnit U.det ∧ IsUnit V.det ∧ p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  set a := M 0 0 with ha_def
  set d := M 1 1 with hd_def
  have hdet' : M.det = a * (d - b' * c' * a) := by
    rw [Matrix.det_fin_two, hb', hc']
    ring
  have hq : d - b' * c' * a ≠ 0 := by
    intro h
    apply hdet
    rw [hdet', h, mul_zero]
  refine ⟨!![1, 0; -c', 1], !![1, -b'; 0, 1], a, d - b' * c' * a, ?_, ?_, ?_, ha, hq⟩
  · refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [diagonalTwo, hb', hc'] <;> ring
  · simp
  · simp

theorem mulS_apply_00 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    (A * Sw) 0 0 = A 0 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]
theorem mulS_apply_01 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    (A * Sw) 0 1 = A 0 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]
theorem mulS_apply_10 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    (A * Sw) 1 0 = A 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]
theorem mulS_apply_11 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    (A * Sw) 1 1 = A 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]
theorem Smul_apply_0 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (j : Fin 2) :
    (Sw * A) 0 j = A 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]
theorem Smul_apply_1 (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (j : Fin 2) :
    (Sw * A) 1 j = A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [Sw]

theorem smith_two (M : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (hdet : M.det ≠ 0) :
    ∃ (U V : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (p q : PowerSeries ℂ),
      U * M * V = diagonalTwo p q ∧ IsUnit U.det ∧ IsUnit V.det ∧ p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨ij, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun ij : Fin 2 × Fin 2 => PowerSeries.order (M ij.1 ij.2)) Finset.univ_nonempty
  have hle : ∀ k l : Fin 2, PowerSeries.order (M ij.1 ij.2) ≤ PowerSeries.order (M k l) :=
    fun k l => hmin (k, l) (Finset.mem_univ _)
  have hne : M ij.1 ij.2 ≠ 0 := by
    intro h0
    apply hdet
    have hall : ∀ k l, M k l = 0 := by
      intro k l
      have := hle k l
      rw [h0, PowerSeries.order_zero, top_le_iff, PowerSeries.order_eq_top] at this
      exact this
    rw [Matrix.det_fin_two, hall 0 0, hall 0 1, hall 1 0, hall 1 1]
    simp
  have hS : IsUnit Sw.det := by
    simp [Sw, Matrix.det_fin_two]
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j
  · -- pivot (0,0)
    simp only [Fin.zero_eta, Fin.isValue] at hle hne
    exact smith_core M hne (dvd_of_order_le hne (hle 0 1)) (dvd_of_order_le hne (hle 1 0)) hdet
  · -- pivot (0,1): use M * S
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hle hne
    have hdet' : (M * Sw).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero hdet hS.ne_zero
    obtain ⟨U, V, p, q, h, hU, hV, hp, hq⟩ := smith_core (M * Sw)
      (by rw [mulS_apply_00]; exact hne)
      (by rw [mulS_apply_00, mulS_apply_01]; exact dvd_of_order_le hne (hle 0 0))
      (by rw [mulS_apply_00, mulS_apply_10]; exact dvd_of_order_le hne (hle 1 1)) hdet'
    refine ⟨U, Sw * V, p, q, ?_, hU, ?_, hp, hq⟩
    · rw [← h]; simp only [Matrix.mul_assoc]
    · rw [Matrix.det_mul]; exact hS.mul hV
  · -- pivot (1,0): use S * M
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hle hne
    have hdet' : (Sw * M).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero hS.ne_zero hdet
    obtain ⟨U, V, p, q, h, hU, hV, hp, hq⟩ := smith_core (Sw * M)
      (by rw [Smul_apply_0]; exact hne)
      (by rw [Smul_apply_0, Smul_apply_0]; exact dvd_of_order_le hne (hle 1 1))
      (by rw [Smul_apply_0, Smul_apply_1]; exact dvd_of_order_le hne (hle 0 0)) hdet'
    refine ⟨U * Sw, V, p, q, ?_, ?_, hV, hp, hq⟩
    · rw [← h]; simp only [Matrix.mul_assoc]
    · rw [Matrix.det_mul]; exact hU.mul hS
  · -- pivot (1,1): use S * M * S
    simp only [Fin.mk_one, Fin.isValue] at hle hne
    have hdet' : (Sw * M * Sw).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hS.ne_zero hdet) hS.ne_zero
    obtain ⟨U, V, p, q, h, hU, hV, hp, hq⟩ := smith_core (Sw * M * Sw)
      (by rw [mulS_apply_00, Smul_apply_0]; exact hne)
      (by rw [mulS_apply_00, mulS_apply_01, Smul_apply_0, Smul_apply_0]
          exact dvd_of_order_le hne (hle 1 0))
      (by rw [mulS_apply_00, mulS_apply_10, Smul_apply_0, Smul_apply_1]
          exact dvd_of_order_le hne (hle 0 1)) hdet'
    refine ⟨U * Sw, Sw * V, p, q, ?_, ?_, ?_, hp, hq⟩
    · rw [← h]; simp only [Matrix.mul_assoc]
    · rw [Matrix.det_mul]; exact hU.mul hS
    · rw [Matrix.det_mul]; exact hS.mul hV


/-- `S` is a formal Taylor series of `F` at `z0`, converging to `F` on the ball of radius `r`. -/
def HasPSAt (z0 : ℂ) (S : PowerSeries ℂ) (F : ℂ → ℂ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ w : ℂ, ‖w‖ < r → HasSum (fun n : ℕ => w ^ n * coeff n S) (F (z0 + w))

theorem HasPSAt.bound {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ} (h : HasPSAt z0 S F r)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r) : ∃ C : ℝ, ∀ n : ℕ, ‖coeff n S‖ * ρ ^ n ≤ C := by
  have hs := (h.2 (ρ : ℂ) (by simpa [abs_of_nonneg hρ0] using hρ)).summable
  have ht := hs.tendsto_atTop_zero
  obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have := hC ⟨n, rfl⟩
  simpa [norm_mul, norm_pow, abs_of_nonneg hρ0, mul_comm] using this

theorem HasPSAt.hasFPowerSeriesOnBall {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ}
    (h : HasPSAt z0 S F r) :
    HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n S)) z0
      (ENNReal.ofReal r) where
  r_le := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro ρ hρ
    have hρr : (ρ : ℝ) < r := by
      rw [← ENNReal.ofReal_coe_nnreal] at hρ
      exact (ENNReal.ofReal_lt_ofReal_iff h.1).1 hρ
    obtain ⟨C, hC⟩ := h.bound ρ.2 hρr
    apply FormalMultilinearSeries.le_radius_of_bound _ C
    intro n
    simpa [FormalMultilinearSeries.ofScalars_norm] using hC n
  r_pos := ENNReal.ofReal_pos.2 h.1
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff h.1).1 hy
    have := h.2 y hy'
    convert this using 1
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]

theorem HasPSAt.analyticAt {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ}
    (h : HasPSAt z0 S F r) : AnalyticAt ℂ F z0 :=
  h.hasFPowerSeriesOnBall.hasFPowerSeriesAt.analyticAt

theorem HasPSAt.summable_norm {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ}
    (h : HasPSAt z0 S F r) {w : ℂ} (hw : ‖w‖ < r) :
    Summable (fun n : ℕ => ‖w ^ n * coeff n S‖) := by
  have hrad : ((‖w‖₊ : NNReal) : ENNReal) < (FormalMultilinearSeries.ofScalars ℂ
      (fun n => coeff n S) : FormalMultilinearSeries ℂ ℂ ℂ).radius := by
    refine lt_of_lt_of_le ?_ h.hasFPowerSeriesOnBall.r_le
    exact ENNReal.coe_lt_ofReal.2 (by simpa using hw)
  have := (FormalMultilinearSeries.ofScalars ℂ
      (fun n => coeff n S) : FormalMultilinearSeries ℂ ℂ ℂ).summable_norm_mul_pow hrad
  refine this.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, coe_nnnorm, mul_comm]

theorem HasPSAt.mul {z0 : ℂ} {S T : PowerSeries ℂ} {F G : ℂ → ℂ} {r : ℝ}
    (h1 : HasPSAt z0 S F r) (h2 : HasPSAt z0 T G r) :
    HasPSAt z0 (S * T) (fun z => F z * G z) r := by
  refine ⟨h1.1, fun w hw => ?_⟩
  have hs1 := h1.summable_norm hw
  have hs2 := h2.summable_norm hw
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hs1 hs2
  have hsm := summable_norm_sum_mul_antidiagonal_of_summable_norm hs1 hs2
  have e1 : (∑' n, w ^ n * coeff n S) = F (z0 + w) := (h1.2 w hw).tsum_eq
  have e2 : (∑' n, w ^ n * coeff n T) = G (z0 + w) := (h2.2 w hw).tsum_eq
  rw [e1, e2] at key
  have hterm : ∀ n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (w ^ kl.1 * coeff kl.1 S) *
      (w ^ kl.2 * coeff kl.2 T) = w ^ n * coeff n (S * T) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hkl
    rw [← this, pow_add]
    ring
  have hh := hsm.of_norm.hasSum
  simp only [hterm] at hh key
  rw [← key] at hh
  exact hh

theorem HasPSAt.sub {z0 : ℂ} {S T : PowerSeries ℂ} {F G : ℂ → ℂ} {r : ℝ}
    (h1 : HasPSAt z0 S F r) (h2 : HasPSAt z0 T G r) :
    HasPSAt z0 (S - T) (fun z => F z - G z) r := by
  refine ⟨h1.1, fun w hw => ?_⟩
  have := (h1.2 w hw).sub (h2.2 w hw)
  convert this using 1
  funext n
  rw [map_sub, mul_sub]

theorem HasPSAt.det_fin_two {z0 : ℂ} {M : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)}
    {F : Fin 2 → Fin 2 → ℂ → ℂ} {r : ℝ} (h : ∀ i j, HasPSAt z0 (M i j) (F i j) r) :
    HasPSAt z0 M.det (fun z => F 0 0 z * F 1 1 z - F 0 1 z * F 1 0 z) r := by
  rw [Matrix.det_fin_two]
  exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))


theorem HasPSAt.shift {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ} (h : HasPSAt z0 S F r)
    (m : ℕ) :
    HasPSAt z0 (PowerSeries.mk fun n => coeff (n + m) S)
      (fun z => ∑' n : ℕ, (z - z0) ^ n * coeff (n + m) S) r := by
  refine ⟨h.1, fun w hw => ?_⟩
  have hsum : Summable (fun n : ℕ => w ^ n * coeff (n + m) S) := by
    by_cases hw0 : w = 0
    · subst hw0
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      have : n ≠ 0 := by simpa using hn
      simp [this]
    · have h1 : Summable (fun n : ℕ => w ^ (n + m) * coeff (n + m) S) :=
        (summable_nat_add_iff m).2 (h.2 w hw).summable
      refine (h1.mul_left ((w ^ m)⁻¹)).congr fun n => ?_
      field_simp
      ring
  simp only [coeff_mk, add_sub_cancel_left]
  exact hsum.hasSum

theorem HasPSAt.analyticOrderAt_eq {z0 : ℂ} {S : PowerSeries ℂ} {F : ℂ → ℂ} {r : ℝ}
    (h : HasPSAt z0 S F r) : analyticOrderAt F z0 = S.order := by
  have hF := h.analyticAt
  by_cases hS : S = 0
  · subst hS
    rw [PowerSeries.order_zero, analyticOrderAt_eq_top]
    filter_upwards [Metric.ball_mem_nhds z0 h.1] with z hz
    have hw : ‖z - z0‖ < r := by simpa [dist_eq_norm] using hz
    have h0 := h.2 (z - z0) hw
    simp only [map_zero, mul_zero] at h0
    have := h0.unique hasSum_zero
    simpa using this
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, S.order = m := ⟨S.order.toNat, (PowerSeries.coe_toNat_order hS).symm⟩
    obtain ⟨hcm, hlt⟩ := PowerSeries.order_eq_nat.1 hm
    rw [hm, hF.analyticOrderAt_eq_natCast]
    have hS' := h.shift m
    refine ⟨fun z => ∑' n : ℕ, (z - z0) ^ n * coeff (n + m) S, hS'.analyticAt, ?_, ?_⟩
    · have : (∑' n : ℕ, (z0 - z0) ^ n * coeff (n + m) S) = coeff m S := by
        rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
        simp
      show (∑' n : ℕ, (z0 - z0) ^ n * coeff (n + m) S) ≠ 0
      rw [this]
      exact hcm
    · filter_upwards [Metric.ball_mem_nhds z0 h.1] with z hz
      have hw : ‖z - z0‖ < r := by simpa [dist_eq_norm] using hz
      have h1 := (hasSum_nat_add_iff' m).2 (h.2 (z - z0) hw)
      have hz0 : ∑ i ∈ Finset.range m, (z - z0) ^ i * coeff i S = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hlt i (Finset.mem_range.1 hi)]; simp
      rw [hz0, sub_zero] at h1
      have h2 := (hS'.2 (z - z0) hw).mul_left ((z - z0) ^ m)
      simp only [coeff_mk, add_sub_cancel_left] at h2
      have h3 : (fun n : ℕ => (z - z0) ^ m * ((z - z0) ^ n * coeff (n + m) S)) =
          fun n : ℕ => (z - z0) ^ (n + m) * coeff (n + m) S := by
        funext n; ring
      rw [h3] at h2
      have := h1.unique h2
      simp only [add_sub_cancel] at this
      simpa [smul_eq_mul] using this



/-! ### Truncated jets `ℂ⟦X⟧ / (X^N)` and kernel dimensions -/

abbrev IdealXN (N : ℕ) : Ideal (PowerSeries ℂ) := Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ N}

abbrev JQ (N : ℕ) := PowerSeries ℂ ⧸ IdealXN N

/-- The quotient map as a ring homomorphism. -/
def jmkR (N : ℕ) : PowerSeries ℂ →+* JQ N := Ideal.Quotient.mk (IdealXN N)

theorem jmkR_eq_zero_iff (N : ℕ) (s : PowerSeries ℂ) :
    jmkR N s = 0 ↔ ∀ k < N, coeff k s = 0 := by
  rw [← PowerSeries.X_pow_dvd_iff, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem jmkR_smul (N : ℕ) (a : ℂ) (s : PowerSeries ℂ) : jmkR N (a • s) = a • jmkR N s :=
  map_smul (Ideal.Quotient.mkₐ ℂ (IdealXN N)) a s

/-- Polynomial series of a coefficient vector. -/
def jser (N : ℕ) (c : Fin N → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if h : k < N then c ⟨k, h⟩ else 0

theorem coeff_jser (N : ℕ) (c : Fin N → ℂ) (k : ℕ) :
    coeff k (jser N c) = if h : k < N then c ⟨k, h⟩ else 0 := coeff_mk _ _

/-- Coefficient vectors to jets. -/
def jext (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] JQ N where
  toFun c := jmkR N (jser N c)
  map_add' c d := by
    rw [← map_add]
    congr 1
    ext k
    simp only [coeff_jser, map_add]
    split_ifs <;> simp
  map_smul' a c := by
    rw [RingHom.id_apply, ← jmkR_smul]
    congr 1
    ext k
    simp only [coeff_jser, map_smul]
    split_ifs <;> simp

theorem jext_apply (N : ℕ) (c : Fin N → ℂ) : jext N c = jmkR N (jser N c) := rfl

theorem jext_injective (N : ℕ) : Function.Injective (jext N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have hc' : jmkR N (jser N c) = 0 := hc
  have := (jmkR_eq_zero_iff N _).1 hc'
  funext j
  have h2 := this j.val j.2
  rw [coeff_jser, dif_pos j.2] at h2
  exact h2

theorem jext_surjective (N : ℕ) : Function.Surjective (jext N) := by
  intro y
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun j => coeff j.val s, ?_⟩
  have h0 : jmkR N (s - jser N fun j : Fin N => coeff j.val s) = 0 := by
    rw [jmkR_eq_zero_iff]
    intro k hk
    simp [coeff_jser, hk]
  rw [map_sub, sub_eq_zero] at h0
  rw [jext_apply, ← h0]
  exact hs

/-- Jets are linearly equivalent to coefficient vectors. -/
def jextEquiv (N : ℕ) : (Fin N → ℂ) ≃ₗ[ℂ] JQ N :=
  LinearEquiv.ofBijective (jext N) ⟨jext_injective N, jext_surjective N⟩

instance jq_finite (N : ℕ) : FiniteDimensional ℂ (JQ N) :=
  LinearEquiv.finiteDimensional (jextEquiv N)

theorem finrank_JQ (N : ℕ) : Module.finrank ℂ (JQ N) = N := by
  rw [← (jextEquiv N).finrank_eq]
  simp

theorem mul_Xpow_jext_zero_iff (N m : ℕ) (hm : m ≤ N) (c : Fin N → ℂ) :
    jmkR N ((PowerSeries.X : PowerSeries ℂ) ^ m) * jext N c = 0 ↔
      ∀ j : Fin (N - m), c ⟨j.val, by omega⟩ = 0 := by
  rw [jext_apply, ← map_mul, jmkR_eq_zero_iff]
  constructor
  · intro h j
    have := h (j.val + m) (by omega)
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, coeff_jser,
      dif_pos (by omega)] at this
    exact this
  · intro h k hk
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hmk
    · rw [coeff_jser, dif_pos (by omega)]
      exact h ⟨k - m, by omega⟩
    · rfl

theorem finrank_ker_mulLeft_Xpow (N m : ℕ) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.mulLeft ℂ
      (jmkR N ((PowerSeries.X : PowerSeries ℂ) ^ m)))) = min N m := by
  by_cases hm : m ≤ N
  · rw [min_eq_right hm]
    let f : (Fin N → ℂ) →ₗ[ℂ] (Fin (N - m) → ℂ) :=
      LinearMap.funLeft ℂ ℂ (Fin.castLE (Nat.sub_le N m))
    have hker : LinearMap.ker (LinearMap.mulLeft ℂ
        (jmkR N ((PowerSeries.X : PowerSeries ℂ) ^ m))) =
        (LinearMap.ker f).map (jextEquiv N).toLinearMap := by
      ext y
      obtain ⟨c, rfl⟩ := jext_surjective N y
      simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply, Submodule.mem_map]
      constructor
      · intro h
        refine ⟨c, ?_, rfl⟩
        funext j
        exact (mul_Xpow_jext_zero_iff N m hm c).1 h j
      · rintro ⟨d, hd, hdy⟩
        have hdc : d = c := jext_injective N hdy
        subst hdc
        refine (mul_Xpow_jext_zero_iff N m hm d).2 fun j => ?_
        exact congrFun hd j
    have hr : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.2
        (LinearMap.funLeft_surjective_of_injective ℂ ℂ _ (Fin.castLE_injective _))
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hr, finrank_top] at this
    simp only [Module.finrank_fin_fun] at this
    rw [hker, LinearEquiv.finrank_map_eq]
    omega
  · have h0 : jmkR N ((PowerSeries.X : PowerSeries ℂ) ^ m) = 0 := by
      rw [jmkR_eq_zero_iff]
      intro k hk
      rw [PowerSeries.coeff_X_pow]
      have : k ≠ m := by omega
      simp [this]
    have hz : LinearMap.mulLeft ℂ (0 : JQ N) = 0 := LinearMap.mulLeft_zero_eq_zero ℂ (JQ N)
    rw [h0, hz, min_eq_left (by omega), LinearMap.ker_zero, finrank_top, finrank_JQ]

theorem finrank_ker_mulLeft (N : ℕ) {p : PowerSeries ℂ} (hp : p ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N p))) =
      min N p.order.toNat := by
  have hu := (PowerSeries.isUnit_divided_by_X_pow_order hp).map (jmkR N)
  have hfa : (PowerSeries.X : PowerSeries ℂ) ^ p.order.toNat * PowerSeries.divXPowOrder p = p :=
    PowerSeries.X_pow_order_mul_divXPowOrder
  have hker : LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N p)) = LinearMap.ker
      (LinearMap.mulLeft ℂ (jmkR N ((PowerSeries.X : PowerSeries ℂ) ^ p.order.toNat))) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply]
    conv_lhs => rw [← hfa]
    rw [map_mul, mul_right_comm]
    exact hu.mul_left_eq_zero
  rw [hker, finrank_ker_mulLeft_Xpow]

/-- `ℂ`-subspace of `(Fin 2 → JQ N)` killed by a matrix. -/
def kerC (N : ℕ) (A : Matrix (Fin 2) (Fin 2) (JQ N)) : Submodule ℂ (Fin 2 → JQ N) :=
  (LinearMap.ker A.mulVecLin).restrictScalars ℂ

theorem mem_kerC {N : ℕ} {A : Matrix (Fin 2) (Fin 2) (JQ N)} {x : Fin 2 → JQ N} :
    x ∈ kerC N A ↔ A.mulVec x = 0 := Iff.rfl

theorem diagonalTwo_map (N : ℕ) (p q : PowerSeries ℂ) :
    (diagonalTwo p q).map (jmkR N) = Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then jmkR N p else jmkR N q) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagonalTwo]

theorem mem_kerC_diag (N : ℕ) (p q : PowerSeries ℂ) (x : Fin 2 → JQ N) :
    x ∈ kerC N ((diagonalTwo p q).map (jmkR N)) ↔ jmkR N p * x 0 = 0 ∧ jmkR N q * x 1 = 0 := by
  rw [mem_kerC, diagonalTwo_map]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.mulVec_diagonal] at h0 h1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · rintro ⟨h0, h1⟩
    funext i
    rw [Matrix.mulVec_diagonal]
    fin_cases i
    · simpa using h0
    · simpa using h1

theorem finrank_kerC_diag (N : ℕ) {p q : PowerSeries ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    Module.finrank ℂ (kerC N ((diagonalTwo p q).map (jmkR N))) =
      min N p.order.toNat + min N q.order.toNat := by
  let E : kerC N ((diagonalTwo p q).map (jmkR N)) →ₗ[ℂ]
      (LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N p))) ×
      (LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N q))) :=
    { toFun := fun x => (⟨x.1 0, (mem_kerC_diag N p q x.1).1 x.2 |>.1⟩,
                         ⟨x.1 1, (mem_kerC_diag N p q x.1).1 x.2 |>.2⟩)
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hE : Function.Bijective E := by
    constructor
    · intro x y hxy
      have h0 : x.1 0 = y.1 0 := congrArg
        (fun z => ((Prod.fst z : LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N p))) : JQ N)) hxy
      have h1 : x.1 1 = y.1 1 := congrArg
        (fun z => ((Prod.snd z : LinearMap.ker (LinearMap.mulLeft ℂ (jmkR N q))) : JQ N)) hxy
      apply Subtype.ext
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hmem : (![a, b] : Fin 2 → JQ N) ∈ kerC N ((diagonalTwo p q).map (jmkR N)) :=
        (mem_kerC_diag N p q _).2 ⟨by simpa using ha, by simpa using hb⟩
      exact ⟨⟨_, hmem⟩, rfl⟩
  rw [(LinearEquiv.ofBijective E hE).finrank_eq, Module.finrank_prod,
    finrank_ker_mulLeft N hp, finrank_ker_mulLeft N hq]

theorem mulVec_inv_mulVec {N : ℕ} (W : Matrix (Fin 2) (Fin 2) (JQ N)) (hW : IsUnit W.det)
    (z : Fin 2 → JQ N) : W⁻¹.mulVec (W.mulVec z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hW, Matrix.one_mulVec]

theorem mulVec_mulVec_inv {N : ℕ} (W : Matrix (Fin 2) (Fin 2) (JQ N)) (hW : IsUnit W.det)
    (z : Fin 2 → JQ N) : W.mulVec (W⁻¹.mulVec z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hW, Matrix.one_mulVec]

/-- Multiplication by an invertible matrix as a `ℂ`-linear equivalence. -/
def equivMat {N : ℕ} (W : Matrix (Fin 2) (Fin 2) (JQ N)) (hW : IsUnit W.det) :
    (Fin 2 → JQ N) ≃ₗ[ℂ] (Fin 2 → JQ N) where
  toFun x := W.mulVec x
  invFun x := W⁻¹.mulVec x
  map_add' x y := Matrix.mulVec_add W x y
  map_smul' a x := by
    simp only [RingHom.id_apply]
    exact Matrix.mulVec_smul W a x
  left_inv x := mulVec_inv_mulVec W hW x
  right_inv x := mulVec_mulVec_inv W hW x

theorem finrank_kerC_conj {N : ℕ} (Mq Uq Vq Dq : Matrix (Fin 2) (Fin 2) (JQ N))
    (h : Uq * Mq * Vq = Dq) (hU : IsUnit Uq.det) (hV : IsUnit Vq.det) :
    Module.finrank ℂ (kerC N Mq) = Module.finrank ℂ (kerC N Dq) := by
  have hmap : kerC N Mq = (kerC N Dq).map (equivMat Vq hV).toLinearMap := by
    ext x
    simp only [Submodule.mem_map, mem_kerC]
    constructor
    · intro hx
      refine ⟨Vq⁻¹.mulVec x, ?_, mulVec_mulVec_inv Vq hV x⟩
      rw [← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_mulVec_inv Vq hV x, hx,
        Matrix.mulVec_zero]
    · rintro ⟨y, hy, rfl⟩
      have h1 : Uq.mulVec (Mq.mulVec (Vq.mulVec y)) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
        exact hy
      have h2 := congrArg (fun z => Uq⁻¹.mulVec z) h1
      simp only [mulVec_inv_mulVec Uq hU, Matrix.mulVec_zero] at h2
      exact h2
  rw [hmap, LinearEquiv.finrank_map_eq]

theorem finrank_kerC_of_smith (N : ℕ) (M U V : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (p q : PowerSeries ℂ) (h : U * M * V = diagonalTwo p q) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    Module.finrank ℂ (kerC N (M.map (jmkR N))) = min N p.order.toNat + min N q.order.toNat := by
  have hh : (U.map (jmkR N)) * (M.map (jmkR N)) * (V.map (jmkR N)) =
      (diagonalTwo p q).map (jmkR N) := by
    rw [← h, Matrix.map_mul, Matrix.map_mul]
  have hU' : IsUnit (U.map (jmkR N)).det := by
    have h1 : (jmkR N) U.det = (U.map (jmkR N)).det := RingHom.map_det (jmkR N) U
    rw [← h1]; exact hU.map _
  have hV' : IsUnit (V.map (jmkR N)).det := by
    have h1 : (jmkR N) V.det = (V.map (jmkR N)).det := RingHom.map_det (jmkR N) V
    rw [← h1]; exact hV.map _
  rw [finrank_kerC_conj _ _ _ _ hh hU' hV', finrank_kerC_diag N hp hq]


/-- Padded coefficient access for a vector-valued jet. -/
def cg (N : ℕ) (c : Fin N → Fin 2 → ℂ) (k : ℕ) : Fin 2 → ℂ :=
  if h : k < N then c ⟨k, h⟩ else 0

/-- Vector-valued coefficient chains versus vector-valued jets. -/
def jvec (N : ℕ) : (Fin N → Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → JQ N) where
  toFun c := fun i => jext N (fun m => c m i)
  invFun y := fun m i => (jextEquiv N).symm (y i) m
  map_add' c d := by
    funext i
    exact (jext N).map_add (fun m => c m i) (fun m => d m i)
  map_smul' a c := by
    funext i
    exact (jext N).map_smul a (fun m => c m i)
  left_inv c := by
    funext m i
    have : (jextEquiv N).symm (jext N (fun m => c m i)) = fun m => c m i :=
      (jextEquiv N).symm_apply_apply (fun m => c m i)
    exact congrFun this m
  right_inv y := by
    funext i
    exact (jextEquiv N).apply_symm_apply (y i)

theorem jvec_apply (N : ℕ) (c : Fin N → Fin 2 → ℂ) (i : Fin 2) :
    jvec N c i = jmkR N (jser N (fun m => c m i)) := rfl

theorem mulVec_jvec_zero_iff (N : ℕ) (M : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (c : Fin N → Fin 2 → ℂ) :
    (M.map (jmkR N)).mulVec (jvec N c) = 0 ↔
      ∀ m : Fin N, ∀ i : Fin 2,
        ∑ a ∈ Finset.range (m.val + 1), ∑ j : Fin 2, coeff a (M i j) * cg N c (m.val - a) j = 0 := by
  have hcomp : ∀ i : Fin 2, (M.map (jmkR N)).mulVec (jvec N c) i =
      jmkR N (∑ j : Fin 2, M i j * jser N (fun m => c m j)) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, jvec_apply, map_sum, map_mul]
  have hcoeff : ∀ (i : Fin 2) (k : ℕ),
      coeff k (∑ j : Fin 2, M i j * jser N (fun m => c m j)) =
        ∑ a ∈ Finset.range (k + 1), ∑ j : Fin 2, coeff a (M i j) * cg N c (k - a) j := by
    intro i k
    rw [map_sum]
    simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_jser, cg]
    split_ifs <;> simp
  constructor
  · intro h m i
    have := congrFun h i
    rw [hcomp i, Pi.zero_apply, jmkR_eq_zero_iff] at this
    rw [← hcoeff i m.val]
    exact this m.val m.2
  · intro h
    funext i
    rw [hcomp i, Pi.zero_apply, jmkR_eq_zero_iff]
    intro k hk
    rw [hcoeff]
    exact h ⟨k, hk⟩ i

end PowerSeriesAlgebra


/-! ### Concrete characteristic Taylor matrix -/

/-- Formal power-series matrix whose entries are the M4 Taylor coefficients of `charMatrix`. -/
def charTaylorMatrix (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun a => tayD bc φ z0 a i j)

theorem coeff_charTaylorMatrix (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) (a : ℕ)
    (i j : Fin 2) : PowerSeries.coeff a (charTaylorMatrix bc φ z0 i j) = tayD bc φ z0 a i j :=
  PowerSeries.coeff_mk _ _

/-- The determinant of the Taylor matrix is a formal Taylor series of
`charConstant bc * boundaryCharacteristic`. -/
theorem charTaylorMatrix_det_hasPS (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) :
    ∃ r : ℝ, HasPSAt z0 (charTaylorMatrix bc φ z0).det
      (fun z => charConstant bc * boundaryCharacteristic φ bc z) r := by
  obtain ⟨r, hr, h⟩ := hasSum_tayD bc φ z0
  refine ⟨r, ?_⟩
  have hent : ∀ i j : Fin 2, HasPSAt z0 (charTaylorMatrix bc φ z0 i j)
      (fun z => charMatrix bc (fundPair φ z ⟨1, zero_le_one, le_rfl⟩) i j) r := by
    intro i j
    refine ⟨hr, fun w hw => ?_⟩
    have := h w hw i j
    simpa only [coeff_charTaylorMatrix] using this
  have hdet := HasPSAt.det_fin_two hent
  have hfun : (fun z => charMatrix bc (fundPair φ z ⟨1, zero_le_one, le_rfl⟩) 0 0 *
        charMatrix bc (fundPair φ z ⟨1, zero_le_one, le_rfl⟩) 1 1 -
        charMatrix bc (fundPair φ z ⟨1, zero_le_one, le_rfl⟩) 0 1 *
        charMatrix bc (fundPair φ z ⟨1, zero_le_one, le_rfl⟩) 1 0) =
      fun z => charConstant bc * boundaryCharacteristic φ bc z := by
    funext z
    rw [← Matrix.det_fin_two]
    exact det_charMatrix_monodromy φ bc z
  rwa [hfun] at hdet

theorem zsKer_subsingleton_of_resolvent {A : SourcePairL2 →ₗ.[ℂ] SourcePairL2} {μ : ℂ}
    (h : HasBoundedResolvent A μ) : Subsingleton (zsKer A μ) := by
  obtain ⟨T, -, hleft⟩ := h
  have key : ∀ w : zsKer A μ, w = 0 := by
    intro w
    obtain ⟨hu, hAu⟩ := w.2
    have h1 := hleft ⟨w.1, hu⟩
    have e : μ • ((⟨w.1, hu⟩ : A.domain) : SourcePairL2) - A ⟨w.1, hu⟩ = 0 := by
      rw [hAu]; simp
    rw [e, map_zero] at h1
    exact Subtype.ext h1.symm
  exact ⟨fun u v => (key u).trans (key v).symm⟩

/-- **M5 (i).** The Taylor germ of the characteristic matrix determinant is not identically
zero: a resolvent point and the identity theorem. -/
theorem charTaylorMatrix_det_ne_zero
    (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) :
    (charTaylorMatrix bc φ z0).det ≠ 0 := by
  intro h0
  have hF : ∀ z : ℂ,
      AnalyticAt ℂ (fun z => charConstant bc * boundaryCharacteristic φ bc z) z := fun z => by
    obtain ⟨r, hr⟩ := charTaylorMatrix_det_hasPS bc φ z
    exact hr.analyticAt
  obtain ⟨r, hr⟩ := charTaylorMatrix_det_hasPS bc φ z0
  have htop : analyticOrderAt (fun z => charConstant bc * boundaryCharacteristic φ bc z) z0 = ⊤ := by
    rw [hr.analyticOrderAt_eq, h0, PowerSeries.order_zero]
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z0 hF).1 htop
  obtain ⟨μ, hμ⟩ := zs_complex_resolvent_nonempty (intervalPotential φ) bc
  have hχ : boundaryCharacteristic φ bc μ = 0 := by
    have h2 := congrFun hzero μ
    simpa [charConstant_ne_zero bc] using h2
  have hnt := (nontrivial_zsKer_iff φ bc μ).2 hχ
  haveI := zsKer_subsingleton_of_resolvent hμ
  exact (not_nontrivial_iff_subsingleton.2 this) hnt

/-- **M5 (ii).** Smith factorization of the Taylor matrix over `ℂ⟦X⟧`, with both invariant
factors allowed to have positive order. -/
theorem exists_smith_factorization_charTaylorMatrix
    (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hdet : (charTaylorMatrix bc φ z0).det ≠ 0) :
    ∃ (U V : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
      (p q : PowerSeries ℂ),
      U * charTaylorMatrix bc φ z0 * V =
        NlsGge.ThirdConsultation.G1.G1104SNF.diagonalTwo p q ∧
      IsUnit U.det ∧ IsUnit V.det ∧ p ≠ 0 ∧ q ≠ 0 :=
  smith_two (charTaylorMatrix bc φ z0) hdet

theorem tayConstraintFun_apply (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) (m : ℕ) (i : Fin 2) :
    tayConstraintFun bc φ z0 c m i =
      ∑ a ∈ Finset.range (m + 1), ∑ j : Fin 2,
        PowerSeries.coeff a (charTaylorMatrix bc φ z0 i j) * cg N c (m - a) j := by
  unfold tayConstraintFun
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mulVec, dotProduct, coeff_charTaylorMatrix]
  rfl

theorem mem_tayKer_iff_mulVec (bc : ZSBoundaryCondition) (φ : PotPair) (z0 : ℂ) {N : ℕ}
    (c : Fin N → PairVec38) :
    c ∈ tayKer bc φ z0 N ↔
      ((charTaylorMatrix bc φ z0).map (jmkR N)).mulVec (jvec N c) = 0 := by
  rw [mem_tayKer_iff, mulVec_jvec_zero_iff]
  constructor
  · intro h m i
    rw [← tayConstraintFun_apply]
    exact congrFun (h m) i
  · intro h m
    funext i
    rw [tayConstraintFun_apply]
    exact h m i

/-- **M5 (iii).** Jet count: for `N` at least the determinant order, the Taylor-coefficient
kernel has dimension equal to the determinant order, whatever the geometric multiplicity. -/
theorem tayKer_finrank_eq_detOrder
    (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (hdet : (charTaylorMatrix bc φ z0).det ≠ 0)
    (hN : ((charTaylorMatrix bc φ z0).det).order.toNat ≤ N) :
    Module.finrank ℂ (tayKer bc φ z0 N) =
      ((charTaylorMatrix bc φ z0).det).order.toNat := by
  obtain ⟨U, V, p, q, hSm, hU, hV, hp, hq⟩ :=
    exists_smith_factorization_charTaylorMatrix φ bc z0 hdet
  have hord := det_order_eq_of_smith_equiv (charTaylorMatrix bc φ z0) U V p q hSm hU hV
  have hker : kerC N ((charTaylorMatrix bc φ z0).map (jmkR N)) =
      (tayKer bc φ z0 N).map (jvec N).toLinearMap := by
    ext y
    simp only [Submodule.mem_map, mem_kerC]
    constructor
    · intro hy
      refine ⟨(jvec N).symm y, ?_, (jvec N).apply_symm_apply y⟩
      rw [mem_tayKer_iff_mulVec]
      simpa using hy
    · rintro ⟨c, hc, rfl⟩
      exact (mem_tayKer_iff_mulVec bc φ z0 c).1 hc
  have h1 : Module.finrank ℂ (tayKer bc φ z0 N) =
      Module.finrank ℂ (kerC N ((charTaylorMatrix bc φ z0).map (jmkR N))) := by
    rw [hker, LinearEquiv.finrank_map_eq]
  rw [h1, finrank_kerC_of_smith N _ U V p q hSm hU hV hp hq]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, p.order = a := ⟨p.order.toNat, (PowerSeries.coe_toNat_order hp).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, q.order = b := ⟨q.order.toNat, (PowerSeries.coe_toNat_order hq).symm⟩
  rw [ha, hb, ← Nat.cast_add] at hord
  have hdn : ((charTaylorMatrix bc φ z0).det).order.toNat = a + b := by
    rw [hord, ENat.toNat_coe]
  rw [ha, hb, ENat.toNat_coe, ENat.toNat_coe]
  rw [hdn] at hN ⊢
  rw [min_eq_right (by omega), min_eq_right (by omega)]

/-- **M5 (iv).** Formal order of the Taylor-matrix determinant equals the analytic order of the
boundary characteristic. -/
theorem charTaylorMatrix_det_order_eq_analyticOrderAt
    (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ)
    (hdet : (charTaylorMatrix bc φ z0).det ≠ 0) :
    PowerSeries.order (charTaylorMatrix bc φ z0).det =
      analyticOrderAt (boundaryCharacteristic φ bc) z0 := by
  have _ := hdet
  obtain ⟨r, hr⟩ := charTaylorMatrix_det_hasPS bc φ z0
  have hk := charConstant_ne_zero bc
  have hχ : AnalyticAt ℂ (boundaryCharacteristic φ bc) z0 := by
    have h2 := (analyticAt_const (v := (charConstant bc)⁻¹)).mul hr.analyticAt
    convert h2 using 1
    funext z
    simp [← mul_assoc, inv_mul_cancel₀ hk]
  rw [← hr.analyticOrderAt_eq]
  exact analyticOrderAt_const_mul (charConstant bc) z0 hk hχ

/-- **M5.** For `N` at least the determinant order, the dimension of the Taylor-coefficient
kernel is the analytic order of the boundary characteristic. -/
theorem concrete_tayKer_finrank_eq_analyticOrderAt
    (φ : PotPair) (bc : ZSBoundaryCondition) (z0 : ℂ) (N : ℕ)
    (hN : ((charTaylorMatrix bc φ z0).det).order.toNat ≤ N) :
    ((Module.finrank ℂ (tayKer bc φ z0 N) : ℕ) : ℕ∞) =
      analyticOrderAt (boundaryCharacteristic φ bc) z0 := by
  have hdet := charTaylorMatrix_det_ne_zero φ bc z0
  rw [tayKer_finrank_eq_detOrder φ bc z0 N hdet hN,
    PowerSeries.coe_toNat_order hdet]
  exact charTaylorMatrix_det_order_eq_analyticOrderAt φ bc z0 hdet

end NlsGge.ThirdConsultation.G1.G1104SNF3

end
