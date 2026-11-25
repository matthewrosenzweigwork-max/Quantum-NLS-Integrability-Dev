import Mathlib

                                                                              
                                                                                                                          
                                                                            
                                                                                                                   
                                                                                                                         
                                                 
                                                                                                 
                                                                                                                       
                           
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.ThirdConsultation.MTraceGen

theorem split_tsum (f : ℤ → ℝ) (hf : Summable f) (L : ℕ) :
    ∑' n : ℤ, f n = (∑ n ∈ Finset.Ioo (-(L : ℤ)) L, f n) +
      ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0) := by
  have h1 : Summable (fun n : ℤ => if n ∈ Finset.Ioo (-(L : ℤ)) L then f n else 0) :=
    summable_of_ne_finset_zero (s := Finset.Ioo (-(L : ℤ)) L) (fun n hn => if_neg hn)
  have h2 : Summable (fun n : ℤ => if L ≤ n.natAbs then f n else 0) := by
    have := hf.sub h1
    refine this.congr (fun n => ?_)
    by_cases hn : n ∈ Finset.Ioo (-(L : ℤ)) L
    · have : ¬ L ≤ n.natAbs := by
        rw [Finset.mem_Ioo] at hn; omega
      simp [hn, this]
    · have : L ≤ n.natAbs := by
        rw [Finset.mem_Ioo] at hn; omega
      simp [hn, this]
  have hpt : (fun n : ℤ => f n) = fun n => (if n ∈ Finset.Ioo (-(L : ℤ)) L then f n else 0) +
      (if L ≤ n.natAbs then f n else 0) := by
    funext n
    by_cases hn : n ∈ Finset.Ioo (-(L : ℤ)) L
    · have : ¬ L ≤ n.natAbs := by
        rw [Finset.mem_Ioo] at hn; omega
      simp [hn, this]
    · have : L ≤ n.natAbs := by
        rw [Finset.mem_Ioo] at hn; omega
      simp [hn, this]
  calc ∑' n : ℤ, f n = ∑' n : ℤ, ((if n ∈ Finset.Ioo (-(L : ℤ)) L then f n else 0) +
        (if L ≤ n.natAbs then f n else 0)) := tsum_congr (fun n => congrFun hpt n)
    _ = _ := by
        rw [h1.tsum_add h2, tsum_eq_sum (s := Finset.Ioo (-(L : ℤ)) L) (fun n hn => if_neg hn)]
        congr 1
        exact Finset.sum_congr rfl (fun n hn => if_pos hn)

theorem tail_anti (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) {L L' : ℕ} (h : L ≤ L') :
    ∑' n : ℤ, (if L' ≤ n.natAbs then f n else 0) ≤ ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0) := by
  have hs : ∀ K : ℕ, Summable (fun n : ℤ => if K ≤ n.natAbs then f n else 0) := fun K =>
    Summable.of_nonneg_of_le (fun n => by split_ifs; exact hf0 n; exact le_rfl)
      (fun n => by split_ifs; exact le_rfl; exact hf0 n) hf
  refine Summable.tsum_le_tsum (fun n => ?_) (hs L') (hs L)
  by_cases h1 : L' ≤ n.natAbs
  · rw [if_pos h1, if_pos (le_trans h h1)]
  · rw [if_neg h1]; split_ifs; exact hf0 n; exact le_rfl

theorem tail_tendsto_zero (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) :
    Tendsto (fun L : ℕ => ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun (L : ℕ) (n : ℤ) => if L ≤ n.natAbs then f n else 0)
    (g := fun _ : ℤ => (0 : ℝ)) (bound := f) hf
    (fun n => tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n.natAbs + 1, fun L hL => by
      show (0 : ℝ) = if L ≤ n.natAbs then f n else 0
      rw [if_neg (by omega)]⟩))
    (Eventually.of_forall (fun L n => by
      by_cases h1 : L ≤ n.natAbs
      · rw [if_pos h1, Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
      · rw [if_neg h1, norm_zero]; exact hf0 n))
  simpa using h

theorem tendsto_tsum_of_uniform_tails (a : ℕ → ℤ → ℝ) (b : ℤ → ℝ)
    (ha0 : ∀ j n, 0 ≤ a j n) (hb0 : ∀ n, 0 ≤ b n)
    (has : ∀ j, Summable (a j)) (hbs : Summable b)
    (hpt : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (b n)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      ∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0) < ε) :
    Tendsto (fun j => ∑' n : ℤ, a j n) atTop (𝓝 (∑' n : ℤ, b n)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨La, hLa⟩ := htail (ε / 3) (by positivity)
  obtain ⟨Lb, hLb⟩ := ((tail_tendsto_zero b hb0 hbs).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).exists
  set L := max La Lb with hL
  set F := Finset.Ioo (-(L : ℤ)) L with hF
  have hfin : Tendsto (fun j => ∑ n ∈ F, a j n) atTop (𝓝 (∑ n ∈ F, b n)) :=
    tendsto_finset_sum F (fun n _ => hpt n)
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hfin (ε / 3) (by positivity)
  refine ⟨J, fun j hj => ?_⟩
  have hJj := hJ j hj
  rw [Real.dist_eq] at hJj ⊢
  rw [split_tsum (a j) (has j) L, split_tsum b hbs L]
  have hta := lt_of_le_of_lt (tail_anti (a j) (ha0 j) (has j) (le_max_left La Lb)) (hLa j)
  have htb := lt_of_le_of_lt (tail_anti b hb0 hbs (le_max_right La Lb)) hLb
  have hta0 : 0 ≤ ∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0) :=
    tsum_nonneg (fun n => by split_ifs; exact ha0 j n; exact le_rfl)
  have htb0 : 0 ≤ ∑' n : ℤ, (if L ≤ n.natAbs then b n else 0) :=
    tsum_nonneg (fun n => by split_ifs; exact hb0 n; exact le_rfl)
  rw [abs_lt] at hJj ⊢
  constructor <;> linarith [hJj.1, hJj.2]

theorem ennreal_tail_to_real (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) (L : ℕ) (ε : ℝ)
    (hε : 0 < ε)
    (h : (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal (f n) else 0) < ENNReal.ofReal ε) :
    ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0) < ε := by
  have hs : Summable (fun n : ℤ => if L ≤ n.natAbs then f n else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs; exact hf0 n; exact le_rfl)
      (fun n => by split_ifs; exact le_rfl; exact hf0 n) hf
  have h0 : ∀ n : ℤ, 0 ≤ (if L ≤ n.natAbs then f n else 0) := fun n => by
    split_ifs; exact hf0 n; exact le_rfl
  have he : (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal (f n) else 0) =
      ENNReal.ofReal (∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg h0 hs]
    refine tsum_congr (fun n => ?_)
    split_ifs <;> simp
  rw [he, ENNReal.ofReal_lt_ofReal_iff hε] at h
  exact h

theorem trace_sign (m : ℕ) (S : ℝ) :
    (-((2 * Complex.I) ^ (2 * m))⁻¹ * ((((-1 : ℝ) ^ (m + 1) * S : ℝ)) : ℂ)).re = S / 4 ^ m := by
  have h1 : (2 * Complex.I) ^ (2 * m) = ((-1 : ℂ) ^ m) * (4 : ℂ) ^ m := by
    rw [pow_mul, mul_pow, Complex.I_sq, ← mul_pow]
    norm_num
  rw [h1]
  push_cast
  rcases neg_one_pow_eq_or ℂ m with h | h
  · rw [h, pow_succ, h]
    have : ((4 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    have e : -(1 * (4 : ℂ) ^ m)⁻¹ * (1 * -1 * (S : ℂ)) = ((S / 4 ^ m : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e, Complex.ofReal_re]
  · rw [h, pow_succ, h]
    have : ((4 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    have e : -(-1 * (4 : ℂ) ^ m)⁻¹ * (-1 * -1 * (S : ℂ)) = ((S / 4 ^ m : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e, Complex.ofReal_re]

end NlsGge.ThirdConsultation.MTraceGen
