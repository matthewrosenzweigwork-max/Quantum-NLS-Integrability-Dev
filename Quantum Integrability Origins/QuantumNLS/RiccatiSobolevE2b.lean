import Mathlib
import QuantumNLS.RiccatiSobolevE1
import QuantumNLS.RiccatiSobolevE2
import QuantumNLS.RiccatiSobolevE2bYoung

/-!
# R-3FEAD88B blocker 2, stage E2b: the periodic H^a algebra property (a > 1/2)

Source convention (DEF-002): `H^a(T_L)` norm `hsq L a c = ∑_k (1 + |2πk/L|)^(2a) |ĉ_k|²` (stage E1).
Convolution of Fourier sequences: `(c*d)_k = ∑_j c_j d_{k-j}` (here `convC`).

Main result, `hsq_convC_le`: for `L > 0`, `1/2 < a`, and `hsq c, hsq d` finite,
`hsq (c*d) ≤ K_a · hsq c · hsq d` with the explicit constant
`K_a = 4 (2^a)² ∑_k (wt_k)⁻¹` (finite by stage E2a `summable_inv_wt`).

Proof outline (Peetre split plus Young ℓ¹·ℓ² with Cauchy-Schwarz):
`(1+|f_k|) ≤ (1+|f_j|) + (1+|f_{k-j}|)` gives `pw_k ≤ 2^a(pw_j + pw_{k-j})`, with `pw_k = (1+|f_k|)^a`.
Hence `pw_k ‖(c*d)_k‖ ≤ 2^a(α_k + β_k)` with `α_k = ∑_j P_j ‖d_{k-j}‖` and `β_k = ∑_j ‖c_j‖ Q_{k-j}`,
`P_j = pw_j ‖c_j‖`, `Q_i = pw_i ‖d_i‖`. Young (`young_tonelli`) bounds the squared `ℓ²` norms by
`(∑‖d‖)² ∑ P²` and `(∑‖c‖)² ∑ Q²`; the `ℓ¹` norms are bounded by `(∑ wt⁻¹)·hsq` (`l1_sq_le`).

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section

open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiSobolevE2bYoung

namespace QuantumNLS.RiccatiSobolevE2b

/-- Convolution of Fourier coefficient sequences `(c*d)_k = ∑_j c_j d_{k-j}`. -/
def convC (c d : ℤ → ℂ) : ℤ → ℂ := fun k => ∑' j : ℤ, c j * d (k - j)

/-- The square root of the weight: `pw_k = (1 + |2πk/L|)^a`, so `wt = pw²`. -/
def pw (L a : ℝ) (k : ℤ) : ℝ := (1 + |freq L k|) ^ a

/-- Weighted sequence `P_j = pw_j ‖c_j‖`. -/
def Pc (L a : ℝ) (c : ℤ → ℂ) (j : ℤ) : ℝ := pw L a j * ‖c j‖

/-- Weighted sequence `Q_i = pw_i ‖d_i‖`. -/
def Qd (L a : ℝ) (d : ℤ → ℂ) (i : ℤ) : ℝ := pw L a i * ‖d i‖

theorem freq_add_sub (L : ℝ) (j k : ℤ) : freq L k = freq L j + freq L (k - j) := by
  unfold freq
  push_cast
  ring

theorem one_add_abs_freq_le (L : ℝ) (j k : ℤ) :
    1 + |freq L k| ≤ (1 + |freq L j|) + (1 + |freq L (k - j)|) := by
  rw [freq_add_sub L j k]
  have h := abs_add_le (freq L j) (freq L (k - j))
  linarith

theorem wt_eq_pw_sq (L a : ℝ) (k : ℤ) : wt L a k = pw L a k ^ 2 := by
  unfold wt pw
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + |freq L k|)]
  congr 1
  push_cast
  ring

theorem pw_nonneg (L a : ℝ) (k : ℤ) : 0 ≤ pw L a k :=
  Real.rpow_nonneg (by positivity) a

theorem one_le_wt {L a : ℝ} (ha : 0 ≤ a) (k : ℤ) : 1 ≤ wt L a k := by
  unfold wt
  exact Real.one_le_rpow (by linarith [abs_nonneg (freq L k)]) (by linarith)

theorem wt_pos {L a : ℝ} (ha : 0 ≤ a) (k : ℤ) : 0 < wt L a k :=
  lt_of_lt_of_le one_pos (one_le_wt ha k)

/-- Finite `H^a` norm gives summability of the weighted squares and the `ENNReal` identity. -/
theorem hsq_summable_eq {L a : ℝ} {c : ℤ → ℂ} (hc : hsq L a c ≠ ⊤) :
    Summable (fun k => wt L a k * ‖c k‖ ^ 2) ∧
      hsq L a c = ENNReal.ofReal (∑' k, wt L a k * ‖c k‖ ^ 2) := by
  have hx0 : ∀ k, 0 ≤ wt L a k * ‖c k‖ ^ 2 := fun k =>
    mul_nonneg (wt_nonneg L a k) (sq_nonneg _)
  have hsum : Summable (fun k => wt L a k * ‖c k‖ ^ 2) := by
    have h := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (wt L a k * ‖c k‖ ^ 2)) hc
    have h2 : Summable (fun k => (ENNReal.ofReal (wt L a k * ‖c k‖ ^ 2)).toReal) := h
    have e : (fun k => (ENNReal.ofReal (wt L a k * ‖c k‖ ^ 2)).toReal)
        = fun k => wt L a k * ‖c k‖ ^ 2 :=
      funext fun k => ENNReal.toReal_ofReal (hx0 k)
    rw [e] at h2
    exact h2
  refine ⟨hsum, ?_⟩
  unfold hsq
  rw [ENNReal.ofReal_tsum_of_nonneg hx0 hsum]

theorem sq_summable_of_wt {L a : ℝ} (ha : 0 ≤ a) {c : ℤ → ℂ}
    (hH : Summable (fun k => wt L a k * ‖c k‖ ^ 2)) : Summable (fun k => ‖c k‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => le_mul_of_one_le_left (sq_nonneg _) (one_le_wt ha k)) hH

theorem l1_summable {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {c : ℤ → ℂ}
    (hH : Summable (fun k => wt L a k * ‖c k‖ ^ 2)) : Summable (fun k => ‖c k‖) := by
  have ha0 : 0 ≤ a := by linarith
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => amgm_l1 (wt_pos ha0 k))
    ((hH.add (summable_inv_wt hL ha)).mul_left (1 / 2))

/-- Two-term bound: `t ≤ p (A + B)`, `t ≥ 0`, gives `t² ≤ 2 p² (A² + B²)`. -/
theorem sq_bound_aux {t A B p : ℝ} (ht : 0 ≤ t) (h : t ≤ p * (A + B)) :
    t ^ 2 ≤ 2 * p ^ 2 * (A ^ 2 + B ^ 2) := by
  have h1 : t ^ 2 ≤ (p * (A + B)) ^ 2 := pow_le_pow_left₀ ht h 2
  have h2 : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by nlinarith [sq_nonneg (A - B)]
  have h3 : p ^ 2 * (A + B) ^ 2 ≤ p ^ 2 * (2 * (A ^ 2 + B ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg p)
  nlinarith [h1, h3]

set_option maxHeartbeats 1000000 in
/-- Main algebra estimate: `hsq (c*d) ≤ K_a hsq c hsq d` for `L > 0`, `a > 1/2`, finite norms. -/
theorem hsq_convC_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (c d : ℤ → ℂ)
    (hc : hsq L a c ≠ ⊤) (hd : hsq L a d ≠ ⊤) :
    hsq L a (convC c d) ≤
      ENNReal.ofReal (4 * (2 ^ a) ^ 2 * ∑' k : ℤ, (wt L a k)⁻¹) * hsq L a c * hsq L a d := by
  have ha0 : 0 ≤ a := by linarith
  have hS : Summable (fun k : ℤ => (wt L a k)⁻¹) := summable_inv_wt hL ha
  have hS0 : 0 ≤ ∑' k : ℤ, (wt L a k)⁻¹ := tsum_nonneg fun k => inv_nonneg.2 (wt_pos ha0 k).le
  obtain ⟨hHc, hEc⟩ := hsq_summable_eq hc
  obtain ⟨hHd, hEd⟩ := hsq_summable_eq hd
  have hHc0 : 0 ≤ ∑' k, wt L a k * ‖c k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (wt_nonneg L a k) (sq_nonneg _)
  have hHd0 : 0 ≤ ∑' k, wt L a k * ‖d k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (wt_nonneg L a k) (sq_nonneg _)
  have hD0 : 0 ≤ ∑' i, ‖d i‖ := tsum_nonneg fun i => norm_nonneg _
  have hE0 : 0 ≤ ∑' i, ‖c i‖ := tsum_nonneg fun i => norm_nonneg _
  have hcc2 : Summable (fun k => ‖c k‖ ^ 2) := sq_summable_of_wt ha0 hHc
  have hcc1 : Summable (fun k => ‖c k‖) := l1_summable hL ha hHc
  have hdd1 : Summable (fun k => ‖d k‖) := l1_summable hL ha hHd
  have hcc0 : ∀ k, 0 ≤ ‖c k‖ := fun k => norm_nonneg _
  have hdd0 : ∀ k, 0 ≤ ‖d k‖ := fun k => norm_nonneg _
  have hPnn : ∀ j, 0 ≤ Pc L a c j := fun j => mul_nonneg (pw_nonneg L a j) (norm_nonneg _)
  have hQnn : ∀ i, 0 ≤ Qd L a d i := fun i => mul_nonneg (pw_nonneg L a i) (norm_nonneg _)
  have hP2 : ∀ j, Pc L a c j ^ 2 = wt L a j * ‖c j‖ ^ 2 := fun j => by
    unfold Pc
    rw [mul_pow, wt_eq_pw_sq]
  have hQ2 : ∀ i, Qd L a d i ^ 2 = wt L a i * ‖d i‖ ^ 2 := fun i => by
    unfold Qd
    rw [mul_pow, wt_eq_pw_sq]
  have hPs : Summable (fun j => Pc L a c j ^ 2) := by simpa only [hP2] using hHc
  have hQs : Summable (fun i => Qd L a d i ^ 2) := by simpa only [hQ2] using hHd
  -- summability of the convolution of norms, and the norm bound for the convolution
  have hnorm_sum : ∀ k, Summable (fun j => ‖c j‖ * ‖d (k - j)‖) := fun k =>
    (young_summable_and_cs hcc0 hdd0 hdd1 hcc2 k).1
  have hnorm : ∀ k, ‖convC c d k‖ ≤ ∑' j, ‖c j‖ * ‖d (k - j)‖ := fun k => by
    calc ‖convC c d k‖ = ‖∑' j, c j * d (k - j)‖ := rfl
      _ ≤ ∑' j, ‖c j * d (k - j)‖ :=
          norm_tsum_le_tsum_norm (by simpa only [norm_mul] using hnorm_sum k)
      _ = ∑' j, ‖c j‖ * ‖d (k - j)‖ := tsum_congr fun j => norm_mul _ _
  -- Peetre split of the weight
  have hpk : ∀ j k, pw L a k ≤ 2 ^ a * (pw L a j + pw L a (k - j)) := fun j k => by
    unfold pw
    calc (1 + |freq L k|) ^ a
        ≤ ((1 + |freq L j|) + (1 + |freq L (k - j)|)) ^ a :=
          Real.rpow_le_rpow (by positivity) (one_add_abs_freq_le L j k) ha0
      _ ≤ 2 ^ a * ((1 + |freq L j|) ^ a + (1 + |freq L (k - j)|) ^ a) :=
          rpow_add_le' (by positivity) (by positivity) ha0
  have hterm : ∀ j k, pw L a k * (‖c j‖ * ‖d (k - j)‖) ≤
      2 ^ a * (Pc L a c j * ‖d (k - j)‖ + ‖c j‖ * Qd L a d (k - j)) := fun j k => by
    have h := mul_le_mul_of_nonneg_right (hpk j k)
      (mul_nonneg (norm_nonneg (c j)) (norm_nonneg (d (k - j))))
    unfold Pc Qd
    calc pw L a k * (‖c j‖ * ‖d (k - j)‖)
        ≤ (2 ^ a * (pw L a j + pw L a (k - j))) * (‖c j‖ * ‖d (k - j)‖) := h
      _ = 2 ^ a * (pw L a j * ‖c j‖ * ‖d (k - j)‖
            + ‖c j‖ * (pw L a (k - j) * ‖d (k - j)‖)) := by ring
  -- summability of the two Peetre pieces
  have hsumA : ∀ k, Summable (fun j => Pc L a c j * ‖d (k - j)‖) := fun k =>
    (young_summable_and_cs hPnn hdd0 hdd1 hPs k).1
  have hsumB : ∀ k, Summable (fun j => ‖c j‖ * Qd L a d (k - j)) := fun k => by
    have h := (young_summable_and_cs hQnn hcc0 hcc1 hQs k).1
    have h' := (Equiv.summable_iff (Equiv.subLeft k)).2 h
    have h2 : Summable (fun j => Qd L a d (k - j) * ‖c j‖) :=
      h'.congr fun j => by
        show Qd L a d (k - j) * ‖c (k - (k - j))‖ = Qd L a d (k - j) * ‖c j‖
        rw [sub_sub_cancel]
    exact h2.congr fun j => mul_comm _ _
  -- pointwise: pw_k ‖(c*d)_k‖ ≤ 2^a (A_k + B_k)
  have hle : ∀ k, pw L a k * ‖convC c d k‖ ≤
      2 ^ a * ((∑' j, Pc L a c j * ‖d (k - j)‖) + ∑' j, ‖c j‖ * Qd L a d (k - j)) := fun k => by
    calc pw L a k * ‖convC c d k‖ ≤ pw L a k * ∑' j, ‖c j‖ * ‖d (k - j)‖ :=
          mul_le_mul_of_nonneg_left (hnorm k) (pw_nonneg L a k)
      _ = ∑' j, pw L a k * (‖c j‖ * ‖d (k - j)‖) := by rw [tsum_mul_left]
      _ ≤ ∑' j, 2 ^ a * (Pc L a c j * ‖d (k - j)‖ + ‖c j‖ * Qd L a d (k - j)) :=
          Summable.tsum_le_tsum (fun j => hterm j k) ((hnorm_sum k).mul_left _)
            (((hsumA k).add (hsumB k)).mul_left _)
      _ = 2 ^ a * ((∑' j, Pc L a c j * ‖d (k - j)‖) + ∑' j, ‖c j‖ * Qd L a d (k - j)) := by
          rw [tsum_mul_left, Summable.tsum_add (hsumA k) (hsumB k)]
  -- reindex the second sum: ∑_j ‖c_j‖ Q_{k-j} = ∑_j Q_j ‖c_{k-j}‖
  have hBk : ∀ k, ∑' j, ‖c j‖ * Qd L a d (k - j) = ∑' j, Qd L a d j * ‖c (k - j)‖ :=
    fun k => tsum_shift_swap (fun j => ‖c j‖) (Qd L a d) k
  have hT : ∀ k, (pw L a k * ‖convC c d k‖) ^ 2 ≤ 2 * (2 ^ a) ^ 2 *
      ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2 + (∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2) := fun k => by
    rw [← hBk k]
    exact sq_bound_aux (mul_nonneg (pw_nonneg L a k) (norm_nonneg _)) (hle k)
  have hfin : ∀ k, ENNReal.ofReal ((pw L a k * ‖convC c d k‖) ^ 2) ≤
      ENNReal.ofReal (2 * (2 ^ a) ^ 2) *
        (ENNReal.ofReal ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2) +
          ENNReal.ofReal ((∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2)) := fun k => by
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * (2 ^ a) ^ 2 by positivity)]
    exact ENNReal.ofReal_le_ofReal (hT k)
  have hsumE : hsq L a (convC c d) = ∑' k, ENNReal.ofReal ((pw L a k * ‖convC c d k‖) ^ 2) := by
    unfold hsq
    refine tsum_congr fun k => ?_
    rw [mul_pow, wt_eq_pw_sq]
  -- Young/Tonelli estimates
  have hA : ∑' k, ENNReal.ofReal ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2) ≤
      ENNReal.ofReal (∑' i, ‖d i‖) ^ 2 * ENNReal.ofReal (∑' i, Pc L a c i ^ 2) :=
    young_tonelli hPnn hdd0 hdd1 hPs
  have hB : ∑' k, ENNReal.ofReal ((∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2) ≤
      ENNReal.ofReal (∑' i, ‖c i‖) ^ 2 * ENNReal.ofReal (∑' i, Qd L a d i ^ 2) :=
    young_tonelli hQnn hcc0 hcc1 hQs
  have hPsum : ∑' i, Pc L a c i ^ 2 = ∑' i, wt L a i * ‖c i‖ ^ 2 := tsum_congr hP2
  have hQsum : ∑' i, Qd L a d i ^ 2 = ∑' i, wt L a i * ‖d i‖ ^ 2 := tsum_congr hQ2
  rw [hPsum] at hA
  rw [hQsum] at hB
  -- l¹ bounds from the weighted l² norms
  have hD : (∑' i, ‖d i‖) ^ 2 ≤ (∑' i, (wt L a i)⁻¹) * ∑' i, wt L a i * ‖d i‖ ^ 2 :=
    l1_sq_le (fun i => wt_pos ha0 i) (fun i => norm_nonneg _) hS hHd
  have hE : (∑' i, ‖c i‖) ^ 2 ≤ (∑' i, (wt L a i)⁻¹) * ∑' i, wt L a i * ‖c i‖ ^ 2 :=
    l1_sq_le (fun i => wt_pos ha0 i) (fun i => norm_nonneg _) hS hHc
  -- abbreviations
  set D := ∑' i, ‖d i‖ with hDdef
  set E := ∑' i, ‖c i‖ with hEdef
  set S := ∑' i, (wt L a i)⁻¹ with hSdef
  set Hc := ∑' i, wt L a i * ‖c i‖ ^ 2 with hHcdef
  set Hd := ∑' i, wt L a i * ‖d i‖ ^ 2 with hHddef
  have hK : (0 : ℝ) ≤ 4 * (2 ^ a) ^ 2 * S := mul_nonneg (by positivity) hS0
  have hA' : ∑' k, ENNReal.ofReal ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2)
      ≤ ENNReal.ofReal (D ^ 2 * Hc) := by
    rw [ENNReal.ofReal_mul (sq_nonneg D), ENNReal.ofReal_pow hD0]
    exact hA
  have hB' : ∑' k, ENNReal.ofReal ((∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2)
      ≤ ENNReal.ofReal (E ^ 2 * Hd) := by
    rw [ENNReal.ofReal_mul (sq_nonneg E), ENNReal.ofReal_pow hE0]
    exact hB
  have hreal : 2 * (2 ^ a) ^ 2 * (D ^ 2 * Hc + E ^ 2 * Hd)
      ≤ 4 * (2 ^ a) ^ 2 * S * Hc * Hd := by
    have h1 : D ^ 2 * Hc ≤ S * Hd * Hc := mul_le_mul_of_nonneg_right hD hHc0
    have h2 : E ^ 2 * Hd ≤ S * Hc * Hd := mul_le_mul_of_nonneg_right hE hHd0
    have h3 : 2 * (2 ^ a) ^ 2 * (D ^ 2 * Hc + E ^ 2 * Hd)
        ≤ 2 * (2 ^ a) ^ 2 * (S * Hd * Hc + S * Hc * Hd) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    calc 2 * (2 ^ a) ^ 2 * (D ^ 2 * Hc + E ^ 2 * Hd)
        ≤ 2 * (2 ^ a) ^ 2 * (S * Hd * Hc + S * Hc * Hd) := h3
      _ = 4 * (2 ^ a) ^ 2 * S * Hc * Hd := by ring
  calc hsq L a (convC c d)
      = ∑' k, ENNReal.ofReal ((pw L a k * ‖convC c d k‖) ^ 2) := hsumE
    _ ≤ ∑' k, ENNReal.ofReal (2 * (2 ^ a) ^ 2) *
          (ENNReal.ofReal ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2) +
            ENNReal.ofReal ((∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2)) :=
        ENNReal.tsum_le_tsum hfin
    _ = ENNReal.ofReal (2 * (2 ^ a) ^ 2) *
          (∑' k, ENNReal.ofReal ((∑' j, Pc L a c j * ‖d (k - j)‖) ^ 2) +
            ∑' k, ENNReal.ofReal ((∑' j, Qd L a d j * ‖c (k - j)‖) ^ 2)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (2 * (2 ^ a) ^ 2) * (ENNReal.ofReal (D ^ 2 * Hc) + ENNReal.ofReal (E ^ 2 * Hd)) :=
        mul_le_mul_of_nonneg_left (add_le_add hA' hB') (by positivity)
    _ = ENNReal.ofReal (2 * (2 ^ a) ^ 2 * (D ^ 2 * Hc + E ^ 2 * Hd)) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * (2 ^ a) ^ 2 by positivity),
          ENNReal.ofReal_add (mul_nonneg (sq_nonneg D) hHc0) (mul_nonneg (sq_nonneg E) hHd0)]
    _ ≤ ENNReal.ofReal (4 * (2 ^ a) ^ 2 * S * Hc * Hd) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (4 * (2 ^ a) ^ 2 * S) * ENNReal.ofReal Hc * ENNReal.ofReal Hd := by
        rw [ENNReal.ofReal_mul (mul_nonneg hK hHc0), ENNReal.ofReal_mul hK]
    _ = ENNReal.ofReal (4 * (2 ^ a) ^ 2 * S) * hsq L a c * hsq L a d := by
        rw [hEc, hEd]

end QuantumNLS.RiccatiSobolevE2b

#print axioms QuantumNLS.RiccatiSobolevE2b.hsq_convC_le
