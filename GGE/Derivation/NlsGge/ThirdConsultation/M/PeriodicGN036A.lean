import Mathlib

set_option autoImplicit false
noncomputable section

open Finset

namespace NlsGge.ThirdConsultation.MPeriodicGN

theorem low_bound (i N K : ℕ) (P : ℕ → ℝ) (T0 : ℝ)
    (h0 : ∀ s : Finset ℕ, ∑ k ∈ s, P k ^ 2 ≤ T0) (hN : 1 ≤ N) :
    (∑ k ∈ (range K).filter (fun k => k ≤ N), (k : ℝ) ^ i * P k) ^ 2 ≤
      2 * (N : ℝ) ^ (2 * i + 1) * T0 := by
  set s := (range K).filter (fun k => k ≤ N) with hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => (k : ℝ) ^ i) P
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ k ∈ s, ((k : ℝ) ^ i) ^ 2 ≤ 2 * (N : ℝ) ^ (2 * i + 1) := by
    have hsub : s ⊆ range (N + 1) := by
      intro k hk
      simp only [hs, Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_range]; omega
    calc ∑ k ∈ s, ((k : ℝ) ^ i) ^ 2
        ≤ ∑ k ∈ range (N + 1), ((k : ℝ) ^ i) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ k ∈ range (N + 1), ((N : ℝ) ^ i) ^ 2 := by
          apply sum_le_sum
          intro k hk
          have : (k : ℝ) ≤ N := by
            have := Finset.mem_range.1 hk
            exact_mod_cast Nat.lt_succ_iff.1 this
          exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) this i) 2
      _ = ((N : ℝ) + 1) * ((N : ℝ) ^ i) ^ 2 := by
          rw [sum_const, card_range]; simp
      _ ≤ 2 * (N : ℝ) * ((N : ℝ) ^ i) ^ 2 := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith [sq_nonneg ((N : ℝ) ^ i)]
      _ = 2 * (N : ℝ) ^ (2 * i + 1) := by ring
  calc _ ≤ (∑ k ∈ s, ((k : ℝ) ^ i) ^ 2) * ∑ k ∈ s, P k ^ 2 := hcs
    _ ≤ (2 * (N : ℝ) ^ (2 * i + 1)) * T0 :=
        mul_le_mul h1 (h0 s) (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

theorem high_bound (i d N K : ℕ) (P : ℕ → ℝ) (Tm : ℝ)
    (hm : ∀ s : Finset ℕ, ∑ k ∈ s, (1 + (k : ℝ) ^ 2) ^ (i + 1 + d) * P k ^ 2 ≤ Tm)
    (hN : 1 ≤ N) :
    (∑ k ∈ (range K).filter (fun k => N < k), (k : ℝ) ^ i * P k) ^ 2 *
        (N : ℝ) ^ (2 * d + 1) ≤ 2 * Tm := by
  set s := (range K).filter (fun k => N < k) with hs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : ∀ k ∈ s, (1 : ℝ) ≤ k := by
    intro k hk
    simp only [hs, Finset.mem_filter] at hk
    exact_mod_cast (by omega : 1 ≤ k)
  have hprod : ∀ k ∈ s, (k : ℝ) ^ i * P k =
      ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) * ((k : ℝ) ^ (i + 1 + d) * P k) := by
    intro k hk
    have : (k : ℝ) ≠ 0 := by have := hk0 k hk; positivity
    field_simp
  rw [sum_congr rfl hprod]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun k => (k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) (fun k => (k : ℝ) ^ (i + 1 + d) * P k)
  have hf : ∑ k ∈ s, ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) ^ 2 ≤
      2 / ((N : ℝ) ^ (2 * d + 1)) := by
    have hsub : s ⊆ Ioo N K := by
      intro k hk
      simp only [hs, Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_Ioo]; omega
    have hterm : ∀ k ∈ s, ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) ^ 2 ≤
        (((N : ℝ) ^ d) ^ 2)⁻¹ * (((k : ℝ) ^ 2)⁻¹) := by
      intro k hk
      have hk1 := hk0 k hk
      have hkN : (N : ℝ) ≤ k := by
        simp only [hs, Finset.mem_filter] at hk
        exact_mod_cast hk.2.le
      have hkp : (0 : ℝ) < k := by linarith
      have e : ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) ^ 2 =
          (((k : ℝ) ^ d) ^ 2)⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
        field_simp
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hkN d) 2
    calc ∑ k ∈ s, ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) ^ 2
        ≤ ∑ k ∈ s, (((N : ℝ) ^ d) ^ 2)⁻¹ * (((k : ℝ) ^ 2)⁻¹) := sum_le_sum hterm
      _ = (((N : ℝ) ^ d) ^ 2)⁻¹ * ∑ k ∈ s, (((k : ℝ) ^ 2)⁻¹) := by rw [mul_sum]
      _ ≤ (((N : ℝ) ^ d) ^ 2)⁻¹ * ∑ k ∈ Ioo N K, (((k : ℝ) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left
            (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity)
      _ ≤ (((N : ℝ) ^ d) ^ 2)⁻¹ * (2 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le N K) (by positivity)
      _ ≤ 2 / ((N : ℝ) ^ (2 * d + 1)) := by
          have h1 : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
          have ha : (0 : ℝ) < ((N : ℝ) ^ d) ^ 2 := by positivity
          have e2 : (N : ℝ) ^ (2 * d + 1) = ((N : ℝ) ^ d) ^ 2 * N := by ring
          rw [e2, ← div_eq_inv_mul, div_div]
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (by nlinarith [ha])
  have hg : ∑ k ∈ s, ((k : ℝ) ^ (i + 1 + d) * P k) ^ 2 ≤ Tm := by
    refine le_trans (sum_le_sum fun k hk => ?_) (hm s)
    rw [mul_pow, ← pow_mul, mul_comm (i + 1 + d) 2, pow_mul]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith [sq_nonneg (1 : ℝ)]) _) (sq_nonneg _)
  have hpos : (0 : ℝ) < (N : ℝ) ^ (2 * d + 1) := by positivity
  calc _ ≤ ((∑ k ∈ s, ((k : ℝ) ^ i / (k : ℝ) ^ (i + 1 + d)) ^ 2) *
        ∑ k ∈ s, ((k : ℝ) ^ (i + 1 + d) * P k) ^ 2) * (N : ℝ) ^ (2 * d + 1) :=
        mul_le_mul_of_nonneg_right hcs hpos.le
    _ ≤ ((2 / (N : ℝ) ^ (2 * d + 1)) * Tm) * (N : ℝ) ^ (2 * d + 1) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul hf hg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ = 2 * Tm := by field_simp


theorem nat_sum_bound (m i : ℕ) (hi : i < m) (P : ℕ → ℝ) (hP : ∀ k, 0 ≤ P k) (T0 Tm : ℝ)
    (hT0 : 0 ≤ T0) (hT0Tm : T0 ≤ Tm)
    (hle0 : ∀ s : Finset ℕ, ∑ k ∈ s, P k ^ 2 ≤ T0)
    (hlem : ∀ s : Finset ℕ, ∑ k ∈ s, (1 + (k : ℝ) ^ 2) ^ m * P k ^ 2 ≤ Tm) :
    Summable (fun k : ℕ => (k : ℝ) ^ i * P k) ∧
    ∑' k : ℕ, (k : ℝ) ^ i * P k ≤
      2 ^ (i + 2) * (T0 ^ ((1 - ((i : ℝ) + 1 / 2) / m) / 2) *
        Tm ^ (((i : ℝ) + 1 / 2) / m / 2)) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = i + 1 + d := ⟨m - i - 1, by omega⟩
  have hmR : (0 : ℝ) < ((i + 1 + d : ℕ) : ℝ) := by positivity
  set θ : ℝ := ((i : ℝ) + 1 / 2) / ((i + 1 + d : ℕ) : ℝ) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hmR]; push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  by_cases hz : T0 = 0
  · have hPz : ∀ k, P k = 0 := by
      intro k
      have : P k ^ 2 ≤ 0 := hz ▸ hle0 {k} |>.trans' (by simp)
      have := sq_nonneg (P k)
      nlinarith [hP k]
    have : (fun k : ℕ => (k : ℝ) ^ i * P k) = fun _ => 0 := by
      funext k; rw [hPz k]; simp
    rw [this]
    refine ⟨summable_zero, ?_⟩
    rw [tsum_zero, hz, Real.zero_rpow (by
      have : 0 < (1 - θ) / 2 := by linarith
      exact this.ne')]
    simp
  have hT0p : 0 < T0 := lt_of_le_of_ne hT0 (Ne.symm hz)
  set lam : ℝ := Tm / T0 with hlam
  have hlam1 : 1 ≤ lam := by rw [hlam, le_div_iff₀ hT0p]; linarith
  set r : ℝ := lam ^ (1 / (2 * ((i + 1 + d : ℕ) : ℝ))) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hlam1 (by positivity)
  have hr0 : 0 < r := by linarith
  have hrpow : r ^ (2 * (i + 1 + d)) = lam := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    push_cast
    have : (1 / (2 * ((i : ℝ) + 1 + d))) * (2 * ((i : ℝ) + 1 + d)) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  have hrθ : r ^ (2 * i + 1) = lam ^ θ := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hθ]
    congr 1
    push_cast
    field_simp
  set N : ℕ := ⌈r⌉₊ with hNdef
  have hNr : r ≤ N := Nat.le_ceil r
  have hN2 : (N : ℝ) ≤ 2 * r := by
    have := Nat.ceil_lt_add_one hr0.le
    linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := hr1.trans hNr
    exact_mod_cast this
  set G : ℝ := T0 ^ ((1 - θ) / 2) * Tm ^ (θ / 2) with hG
  have hTm0 : 0 ≤ Tm := hT0.trans hT0Tm
  have hG0 : 0 ≤ G := mul_nonneg (Real.rpow_nonneg hT0 _) (Real.rpow_nonneg hTm0 _)
  have e1 : (T0 ^ ((1 - θ) / 2)) ^ 2 = T0 ^ (1 - θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]; congr 1; push_cast; ring
  have e2 : (Tm ^ (θ / 2)) ^ 2 = Tm ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTm0]; congr 1; push_cast; ring
  have e3 : T0 * lam ^ θ = T0 ^ (1 - θ) * Tm ^ θ := by
    rw [hlam, Real.div_rpow hTm0 hT0, Real.rpow_sub hT0p, Real.rpow_one]
    have : 0 < T0 ^ θ := Real.rpow_pos_of_pos hT0p θ
    field_simp
  have hG2 : G ^ 2 = T0 * r ^ (2 * i + 1) := by
    rw [hG, mul_pow, e1, e2, hrθ, e3]
  set L : ℝ := 2 ^ (i + 1) * G with hL
  have hL2 : L ^ 2 = 2 ^ (2 * i + 2) * (T0 * r ^ (2 * i + 1)) := by
    rw [hL, mul_pow, hG2, ← pow_mul]; congr 2; ring
  have hL0 : 0 ≤ L := by positivity
  have hfin : ∀ K : ℕ, ∑ k ∈ range K, (k : ℝ) ^ i * P k ≤ 2 * L := by
    intro K
    rw [← sum_filter_add_sum_filter_not (range K) (fun k => k ≤ N)]
    have hlow := low_bound i N K P T0 hle0 hN1
    have hhigh := high_bound i d N K P Tm hlem hN1
    have hlow' : (∑ k ∈ (range K).filter (fun k => k ≤ N), (k : ℝ) ^ i * P k) ≤ L := by
      refine (sq_le_sq₀ (sum_nonneg fun k _ => by have := hP k; positivity) hL0).1 ?_
      refine hlow.trans ?_
      rw [hL2]
      have hNp : (N : ℝ) ^ (2 * i + 1) ≤ (2 * r) ^ (2 * i + 1) :=
        pow_le_pow_left₀ (by positivity) hN2 _
      calc 2 * (N : ℝ) ^ (2 * i + 1) * T0 ≤ 2 * (2 * r) ^ (2 * i + 1) * T0 := by gcongr
        _ = 2 ^ (2 * i + 2) * (T0 * r ^ (2 * i + 1)) := by ring
    have hnot : (range K).filter (fun k => ¬ k ≤ N) = (range K).filter (fun k => N < k) := by
      apply filter_congr; intro k _; omega
    rw [hnot]
    have hhigh' : (∑ k ∈ (range K).filter (fun k => N < k), (k : ℝ) ^ i * P k) ≤ L := by
      refine (sq_le_sq₀ (sum_nonneg fun k _ => by have := hP k; positivity) hL0).1 ?_
      have hNp : r ^ (2 * d + 1) ≤ (N : ℝ) ^ (2 * d + 1) := pow_le_pow_left₀ hr0.le hNr _
      have hrp : 0 < r ^ (2 * d + 1) := by positivity
      have hTm : Tm = r ^ (2 * (i + 1 + d)) * T0 := by rw [hrpow, hlam]; field_simp
      rw [hL2]
      have h3 : (∑ k ∈ (range K).filter (fun k => N < k), (k : ℝ) ^ i * P k) ^ 2 * r ^ (2 * d + 1)
          ≤ 2 * Tm := le_trans (mul_le_mul_of_nonneg_left hNp (sq_nonneg _)) hhigh
      have h4 : 2 * Tm = 2 * (T0 * r ^ (2 * i + 1)) * r ^ (2 * d + 1) := by
        rw [hTm]; ring
      rw [h4] at h3
      have := le_of_mul_le_mul_right h3 hrp
      refine this.trans ?_
      have : (1 : ℝ) ≤ 2 ^ (2 * i + 1) := one_le_pow₀ (by norm_num)
      have hp : 0 ≤ T0 * r ^ (2 * i + 1) := by positivity
      calc 2 * (T0 * r ^ (2 * i + 1)) ≤ 2 ^ (2 * i + 1) * 2 * (T0 * r ^ (2 * i + 1)) := by
            nlinarith
        _ = 2 ^ (2 * i + 2) * (T0 * r ^ (2 * i + 1)) := by ring
    linarith
  have hnn : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ i * P k := fun k => by have := hP k; positivity
  refine ⟨summable_of_sum_range_le hnn hfin, ?_⟩
  refine (Real.tsum_le_of_sum_range_le hnn hfin).trans ?_
  rw [hL, hG]; ring_nf; rfl


theorem aux_neg (i : ℕ) (c : ℤ → ℝ) (k : ℕ) :
    |((-((k : ℤ) + 1) : ℤ) : ℝ)| ^ i * c (-((k : ℤ) + 1)) =
      (((k + 1 : ℕ) : ℝ)) ^ i * c (-((k + 1 : ℕ) : ℤ)) := by
  have e : (-(((k + 1 : ℕ)) : ℤ)) = -((k : ℤ) + 1) := by push_cast; ring
  rw [e, show (((-((k : ℤ) + 1) : ℤ)) : ℝ) = -((k : ℝ) + 1) by push_cast; ring, abs_neg,
    abs_of_nonneg (by positivity)]
  push_cast; ring_nf

theorem sum_le_of_inj (φ : ℕ → ℤ) (hφ : Function.Injective φ) (F : ℤ → ℝ)
    (hF : ∀ n, 0 ≤ F n) (T : ℝ) (h : HasSum F T) (s : Finset ℕ) :
    ∑ k ∈ s, F (φ k) ≤ T := by
  have := sum_le_hasSum (s.image φ) (fun k _ => hF k) h
  rwa [sum_image (fun x _ y _ hxy => hφ hxy)] at this

theorem cast_inj : Function.Injective (fun k : ℕ => (k : ℤ)) := fun x y h => Int.ofNat.inj h

theorem negcast_inj : Function.Injective (fun k : ℕ => -(k : ℤ)) := fun x y h => by
  have : (x : ℤ) = y := neg_injective h
  exact Int.ofNat.inj this

theorem aux_pos (i : ℕ) (c : ℤ → ℝ) (k : ℕ) :
    |((k : ℤ) : ℝ)| ^ i * c (k : ℤ) = (k : ℝ) ^ i * c (k : ℤ) := by
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]

theorem int_sum_bound (m i : ℕ) (hi : i < m) (c : ℤ → ℝ) (hc : ∀ n, 0 ≤ c n) (T0 Tm : ℝ)
    (h0 : HasSum (fun n : ℤ => c n ^ 2) T0)
    (hm : HasSum (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * c n ^ 2) Tm) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ i * c n) ∧
    ∑' n : ℤ, |(n : ℝ)| ^ i * c n ≤
      2 ^ (i + 3) * (T0 ^ ((1 - ((i : ℝ) + 1 / 2) / m) / 2) *
        Tm ^ (((i : ℝ) + 1 / 2) / m / 2)) := by
  have hT0 : 0 ≤ T0 := h0.nonneg (fun k => sq_nonneg _)
  have hT0Tm : T0 ≤ Tm := by
    refine hasSum_le (fun k => ?_) h0 hm
    have : (1 : ℝ) ≤ (1 + (k : ℝ) ^ 2) ^ m :=
      one_le_pow₀ (by nlinarith [sq_nonneg (k : ℝ)])
    nlinarith [sq_nonneg (c k)]
  have hP := nat_sum_bound m i hi (fun k : ℕ => c k) (fun k => hc _) T0 Tm hT0 hT0Tm
    (fun s => sum_le_of_inj _ cast_inj (fun n => c n ^ 2) (fun n => sq_nonneg _) T0 h0 s)
    (fun s => sum_le_of_inj _ cast_inj (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * c n ^ 2)
      (fun n => by have := hc n; positivity) Tm hm s)
  have hQ := nat_sum_bound m i hi (fun k : ℕ => c (-(k : ℤ))) (fun k => hc _) T0 Tm hT0 hT0Tm
    (fun s => sum_le_of_inj _ negcast_inj (fun n => c n ^ 2) (fun n => sq_nonneg _) T0 h0 s)
    (fun s => by
      have := sum_le_of_inj _ negcast_inj (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * c n ^ 2)
        (fun n => by have := hc n; positivity) Tm hm s
      simpa using this)
  obtain ⟨hPs, hPt⟩ := hP
  obtain ⟨hQs, hQt⟩ := hQ
  have hf1 : Summable (fun k : ℕ => |((k : ℤ) : ℝ)| ^ i * c (k : ℤ)) :=
    hPs.congr (fun k => (aux_pos i c k).symm)
  have hf2' := (summable_nat_add_iff 1).2 hQs
  have hf2 : Summable (fun k : ℕ => |((-((k : ℤ) + 1) : ℤ) : ℝ)| ^ i * c (-((k : ℤ) + 1))) := by
    refine hf2'.congr (fun k => ?_)
    rw [aux_neg]
  have hsum := Summable.of_nat_of_neg_add_one (f := fun n : ℤ => |(n : ℝ)| ^ i * c n) hf1 hf2
  refine ⟨hsum, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => |(n : ℝ)| ^ i * c n) hf1 hf2]
  have h1 : ∑' k : ℕ, |((k : ℤ) : ℝ)| ^ i * c (k : ℤ) = ∑' k : ℕ, (k : ℝ) ^ i * c k := by
    exact tsum_congr (fun k => aux_pos i c k)
  have h2 : ∑' k : ℕ, |((-((k : ℤ) + 1) : ℤ) : ℝ)| ^ i * c (-((k : ℤ) + 1)) ≤
      ∑' k : ℕ, (k : ℝ) ^ i * c (-(k : ℤ)) := by
    have e := hQs.tsum_eq_zero_add
    have hnn : 0 ≤ (((0 : ℕ) : ℝ)) ^ i * c (-((0 : ℕ) : ℤ)) := by
      have := hc (-((0 : ℕ) : ℤ)); positivity
    have e2 : ∑' k : ℕ, |((-((k : ℤ) + 1) : ℤ) : ℝ)| ^ i * c (-((k : ℤ) + 1)) =
        ∑' k : ℕ, (((k + 1 : ℕ) : ℝ)) ^ i * c (-((k + 1 : ℕ) : ℤ)) := by
      refine tsum_congr (fun k => ?_); rw [aux_neg]
    rw [e2]; linarith
  rw [h1]
  set X : ℝ := T0 ^ ((1 - ((i : ℝ) + 1 / 2) / m) / 2) *
        Tm ^ (((i : ℝ) + 1 / 2) / m / 2) with hX
  have e4 : (2 : ℝ) ^ (i + 3) * X = 2 ^ (i + 2) * X + 2 ^ (i + 2) * X := by ring
  rw [e4]
  linarith

theorem holder_bound (m j : ℕ) (hj : j ≤ m) (hm0 : 0 < m) (x : ℤ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (T0 Tm : ℝ) (h0 : HasSum x T0)
    (hm : HasSum (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * x n) Tm) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ j * x n) ∧
    ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ j * x n ≤ Tm ^ ((j : ℝ) / m) * T0 ^ (1 - (j : ℝ) / m) := by
  have hw : ∀ n : ℤ, (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := fun n => by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · simp only [pow_zero, one_mul, Nat.cast_zero, zero_div, Real.rpow_zero, sub_zero,
      Real.rpow_one, one_mul]
    exact ⟨h0.summable, h0.tsum_eq.le⟩
  rcases hj.eq_or_lt with rfl | hjm
  · simp only [div_self hmR.ne', Real.rpow_one, sub_self, Real.rpow_zero, mul_one]
    exact ⟨hm.summable, hm.tsum_eq.le⟩
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjp
  have hjmR : (j : ℝ) < m := by exact_mod_cast hjm
  set a : ℝ := (j : ℝ) / m with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha, div_lt_one hmR]; exact hjmR
  have hpq : (a⁻¹).HolderConjugate ((1 - a)⁻¹) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [one_lt_inv₀ ha0]; exact ha1, ?_⟩
    rw [inv_inv, inv_inv]; ring
  have hT0 : 0 ≤ T0 := h0.nonneg hx
  have hTm : 0 ≤ Tm := hm.nonneg (fun n => mul_nonneg (pow_nonneg (hw n) _) (hx n))
  let f : ℤ → ℝ := fun n => ((1 + (n : ℝ) ^ 2) ^ m * x n) ^ a
  let g : ℤ → ℝ := fun n => x n ^ (1 - a)
  have hf : ∀ n, 0 ≤ f n := fun n =>
    Real.rpow_nonneg (mul_nonneg (pow_nonneg (hw n) _) (hx n)) _
  have hg : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (hx n) _
  have hfp : ∀ n, f n ^ a⁻¹ = (1 + (n : ℝ) ^ 2) ^ m * x n := fun n => by
    simp only [f]
    rw [← Real.rpow_mul (mul_nonneg (pow_nonneg (hw n) _) (hx n)), mul_inv_cancel₀ ha0.ne',
      Real.rpow_one]
  have hgq : ∀ n, g n ^ (1 - a)⁻¹ = x n := fun n => by
    simp only [g]
    rw [← Real.rpow_mul (hx n), mul_inv_cancel₀ (by linarith), Real.rpow_one]
  have hfs : Summable (fun n => f n ^ a⁻¹) := by simpa only [hfp] using hm.summable
  have hgs : Summable (fun n => g n ^ (1 - a)⁻¹) := by simpa only [hgq] using h0.summable
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hfs hgs
  have hfg : ∀ n, f n * g n = (1 + (n : ℝ) ^ 2) ^ j * x n := by
    intro n
    simp only [f, g]
    rw [Real.mul_rpow (pow_nonneg (hw n) _) (hx n)]
    have e1 : ((1 + (n : ℝ) ^ 2) ^ m) ^ a = (1 + (n : ℝ) ^ 2) ^ j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hw n), ha]
      rw [show (m : ℝ) * ((j : ℝ) / m) = j by field_simp, Real.rpow_natCast]
    rw [e1, mul_assoc, ← Real.rpow_add' (hx n) (by linarith)]
    have : a + (1 - a) = 1 := by ring
    rw [this, Real.rpow_one]
  simp only [hfg] at hsum hle
  refine ⟨hsum, hle.trans ?_⟩
  rw [tsum_congr hfp, tsum_congr hgq, hm.tsum_eq, h0.tsum_eq, one_div, one_div, inv_inv, inv_inv]

end NlsGge.ThirdConsultation.MPeriodicGN
