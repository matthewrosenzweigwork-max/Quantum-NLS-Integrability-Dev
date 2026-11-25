import Mathlib
import QuantumNLS.Ext006CoreLimit
import QuantumNLS.Prop023FiniteModeLimit
import QuantumNLS.Prop023SpectralMoments
import QuantumNLS.Prop023Scalar

/-! PROP-023 `Q7B:lem:moments` on the actual physical Fock space.

`prop023_weak_moments` : for a normalized physical weak vacuum `x` (the weak annihilation equation
`Ext006PhysicalVacuum.PhysicalWeakVacuum K x` for a symmetric kernel `K`, no Hilbert-Schmidt or
operator-norm premise) with spectral mean number `<x, N x> <= Q - 1`, `Q >= 1`:

  `exponentialMoment Q x <= e^{1/4}`   and   `||(N + j)^{j/2} x|| <= (32 Q j)^{j/2}`  (`j >= 1`).

Route: `Ext006CoreLimit.weak_vacuum_recurrence` (the sector probabilities `p_n = ||x_{2n}||²`
satisfy `2 n p_n = sum t_m p_{n-m}` with `t` nonnegative and submultiplicative), then the scalar
Riccati bound `Prop023Scalar.exp_moment_partial`, then the frozen `Prop023SpectralMoments`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal
namespace QuantumNLS.Prop023Number
open Occupation Ext006CoreLimit Ext006VacuumRecurrence Ext006PhysicalVacuum Ext006NumberPhase
  Prop023FiniteModeLimit Ext025B3PhysicalSectors Filter Topology
variable {L : ℝ} [Fact (0 < L)]

/-! ### 1. Sector probabilities of a physical vector -/

lemma summable_normSq (x : Fock L) : Summable fun m : Occ => Complex.normSq (coefficient x m) := by
  have h1 : (∑' m : Occ, mass x m) = ENNReal.ofReal (∑' n : ℕ, ‖x n‖ ^ 2) := by
    have := numberExpectation_eq_occupation x (fun _ => 1)
    simp only [one_mul] at this
    rw [← this]
    unfold numberExpectation
    simp only [one_mul]
    have hs := lp.hasSum_norm (E := fun n => BetheCoefficientTransform.HN L n) (p := 2)
      (by norm_num) x
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable)]
  have h2 : (∑' m : Occ, mass x m) ≠ ⊤ := by rw [h1]; exact ENNReal.ofReal_ne_top
  have := ENNReal.summable_toReal h2
  refine this.congr fun m => ?_
  unfold mass
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.sq_norm]

/-- The sector probability of the occupation coefficients is the squared sector norm. -/
lemma sector_prob (x : Fock L) (N : ℕ) :
    (∑' m : Occ, if total m = N then Complex.normSq (coefficient x m) else 0) = ‖x N‖ ^ 2 := by
  classical
  have hsum := summable_normSq x
  have hnn : ∀ m : Occ, 0 ≤ (if total m = N then Complex.normSq (coefficient x m) else 0) :=
    fun m => by split_ifs <;> simp [Complex.normSq_nonneg]
  have hsum' : Summable fun m : Occ =>
      (if total m = N then Complex.normSq (coefficient x m) else 0) :=
    hsum.of_nonneg_of_le hnn fun m => by split_ifs <;> simp [Complex.normSq_nonneg]
  have h1 : ENNReal.ofReal (∑' m : Occ, if total m = N then Complex.normSq (coefficient x m) else 0)
      = ENNReal.ofReal (‖x N‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum', ← sector_mass x N]
    have : (fun m : Occ => ENNReal.ofReal (if total m = N then Complex.normSq (coefficient x m)
        else 0)) = Set.indicator {m : Occ | total m = N} (fun m => mass x m) := by
      funext m
      unfold mass
      by_cases h : total m = N
      · simp [h, Complex.sq_norm]
      · simp [h]
    rw [this, ← tsum_subtype]
    rfl
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn) (sq_nonneg _)).1 h1

/-- Odd sectors of a weak vacuum vanish. -/
lemma odd_zero {K : Kernel} (hK : ∀ i j, K i j = K j i) {ξ : Occ → ℂ} (hξ : WeakVacuum K ξ)
    {m : Occ} (hm : ¬ Even (total m)) : ξ m = 0 := by
  classical
  set Z : Occ → ℂ := fun m => if Even (total m) then 0 else ξ m with hZ
  have hZv : WeakVacuum K Z := by
    intro a m
    rcases Nat.even_or_odd (total m) with he | ho
    · have h1 : ¬ Even (total (m + e a)) := by
        rw [total_add_e]; obtain ⟨r, hr⟩ := he; rw [hr]; intro h; obtain ⟨q, hq⟩ := h; omega
      have h := hξ a m
      simp only [hZ, h1, if_false]
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
      have ht := total_sub_e hb'
      have h2 : ¬ Even (total (m - e b)) := by
        obtain ⟨r, hr⟩ := he; intro h; obtain ⟨q, hq⟩ := h; omega
      simp [h2]
    · have h1 : Even (total (m + e a)) := by
        rw [total_add_e]; obtain ⟨r, hr⟩ := ho; exact ⟨r + 1, by omega⟩
      simp only [hZ, h1, if_true, mul_zero]
      symm
      rw [neg_eq_zero]
      apply Finset.sum_eq_zero
      intro b hb
      have hb' : 1 ≤ m b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
      have ht := total_sub_e hb'
      have h2 : Even (total (m - e b)) := by
        obtain ⟨r, hr⟩ := ho; exact ⟨r, by omega⟩
      simp [h2]
  have h0 : Z 0 = 0 := by simp [hZ, total]
  have := coefficients_zero_of_vacuum_zero hZv h0 m
  simpa [hZ, hm] using this

/-- `p_n = ||x_{2n}||²` equals the sector probability `pAll` of the coefficients. -/
lemma pAll_eq (x : Fock L) (n : ℕ) : pAll (coefficient x) n = ‖x (2 * n)‖ ^ 2 :=
  sector_prob x (2 * n)

/-! ### 2. The physical number law -/

theorem prop023_weak {K : Kernel} (hK : ∀ i j, K i j = K j i) (x : Fock L) (hx : ‖x‖ = 1)
    (hv : PhysicalWeakVacuum K x) {Q : ℝ} (hQ : 1 ≤ Q)
    (hN : numberExpectation (fun n => (n : ℝ≥0∞)) x ≤ ENNReal.ofReal (Q - 1)) :
    exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hξ : WeakVacuum K (coefficient x) := hv
  have hξ0 : coefficient x 0 ≠ 0 := physical_vacuum_coefficient_ne_zero hv hx
  have hsum := summable_normSq x
  obtain ⟨t, ht, hrec⟩ := weak_vacuum_recurrence K hK hξ hξ0 hsum
  set p : ℕ → ℝ := fun n => ‖x (2 * n)‖ ^ 2 with hp
  have hpnn : ∀ n, 0 ≤ p n := fun n => sq_nonneg _
  have hrec' : ∀ n : ℕ, 2 * (n : ℝ) * p n =
      ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, t y.1 * p y.2 := by
    intro n
    have := hrec n
    simpa only [hp, pAll_eq] using this
  -- odd sectors vanish
  have hodd : ∀ N : ℕ, ¬ Even N → ‖x N‖ = 0 := by
    intro N hN
    have h0 : ∀ m : Occ, total m = N → coefficient x m = 0 := fun m hm =>
      odd_zero hK hξ (by rw [hm]; exact hN)
    have h1 := sector_prob x N
    have h2 : (∑' m : Occ, if total m = N then Complex.normSq (coefficient x m) else 0) = 0 := by
      rw [← tsum_zero]
      refine tsum_congr fun m => ?_
      by_cases h : total m = N
      · simp [h, h0 m h]
      · simp [h]
    rw [h2] at h1
    exact (pow_eq_zero_iff two_ne_zero).1 h1.symm
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by simpa using h
  have hrange : ∀ N : ℕ, N ∉ Set.range (fun n : ℕ => 2 * n) → ‖x N‖ ^ 2 = 0 := by
    intro N hN
    have : ¬ Even N := by
      rintro ⟨r, hr⟩
      exact hN ⟨r, by simp; omega⟩
    rw [hodd N this]; norm_num
  have hs2 : HasSum (fun N : ℕ => ‖x N‖ ^ 2) 1 := by
    have h := lp.hasSum_norm (E := fun n => BetheCoefficientTransform.HN L n) (p := 2)
      (by norm_num) x
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hx, one_pow] using h
  have hps : HasSum p 1 := by
    have := (hinj.hasSum_iff (f := fun N : ℕ => ‖x N‖ ^ 2) (a := 1) hrange).2 hs2
    simpa [hp, Function.comp_def] using this
  have htot : Tendsto (fun N => ∑ n ∈ Finset.range N, p n) atTop (nhds 1) := hps.tendsto_sum_nat
  -- the mean number bounds the partial sums
  have hE : ∀ M, ∑ n ∈ Finset.range (M + 1), 2 * (n : ℝ) * p n ≤ Q - 1 := by
    intro M
    have h1 : ENNReal.ofReal (∑ n ∈ Finset.range (M + 1), 2 * (n : ℝ) * p n) ≤
        numberExpectation (fun n => (n : ℝ≥0∞)) x := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by have := hpnn n; positivity)]
      unfold numberExpectation
      calc ∑ n ∈ Finset.range (M + 1), ENNReal.ofReal (2 * (n : ℝ) * p n)
          = ∑ N ∈ (Finset.range (M + 1)).image (fun n : ℕ => 2 * n),
              ((N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (‖x N‖ ^ 2) := by
            rw [Finset.sum_image (fun a _ b _ h => hinj h)]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.sum_le_tsum _
    have h2 := h1.trans hN
    have hQ1 : 0 ≤ Q - 1 := by linarith
    exact (ENNReal.ofReal_le_ofReal_iff hQ1).1 h2
  have hB : ∀ M, ∑ k ∈ Finset.range (M + 1), t k ≤ Q - 1 :=
    fun M => Prop023Scalar.partial_t_le ht hpnn hrec' hE htot M
  -- the exponential moment
  unfold exponentialMoment numberExpectation
  have hsupp : Function.support (fun N : ℕ => ENNReal.ofReal (Real.exp ((N : ℝ) / (16 * Q))) *
      ENNReal.ofReal (‖x N‖ ^ 2)) ⊆ Set.range (fun n : ℕ => 2 * n) := by
    intro N hN
    by_contra hcon
    have h0 : ‖x N‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 (hrange N hcon)
    apply hN
    simp [h0]
  rw [← hinj.tsum_eq hsupp]
  apply ENNReal.tsum_le_of_sum_range_le
  intro M
  cases M with
  | zero => simp
  | succ M =>
    have hb := Prop023Scalar.exp_moment_partial ht hpnn hrec' hQ hB M
    have hle1 : ∑ n ∈ Finset.range (M + 1), p n ≤ 1 :=
      sum_le_hasSum _ (fun n _ => hpnn n) hps
    have hexp : ∀ n : ℕ, Real.exp (((2 * n : ℕ) : ℝ) / (16 * Q)) = Real.exp (1 / (8 * Q)) ^ n := by
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      ring
    calc ∑ n ∈ Finset.range (M + 1), ENNReal.ofReal (Real.exp (((2 * n : ℕ) : ℝ) / (16 * Q))) *
          ENNReal.ofReal (‖x (2 * n)‖ ^ 2)
        = ENNReal.ofReal (∑ n ∈ Finset.range (M + 1),
            p n * Real.exp (1 / (8 * Q)) ^ n) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hpnn n) (by positivity))]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hexp n, ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          calc _ ≤ Real.exp (1 / 4 : ℝ) * ∑ n ∈ Finset.range (M + 1), p n := hb
            _ ≤ Real.exp (1 / 4 : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hle1 (Real.exp_pos _).le
            _ = _ := mul_one _

/-- **PROP-023 `Q7B:lem:moments`** on the physical Fock space, for a normalized weak vacuum. -/
theorem prop023_weak_moments {K : Kernel} (hK : ∀ i j, K i j = K j i) (x : Fock L) (hx : ‖x‖ = 1)
    (hv : PhysicalWeakVacuum K x) {Q : ℝ} (hQ : 1 ≤ Q)
    (hN : numberExpectation (fun n => (n : ℝ≥0∞)) x ≤ ENNReal.ofReal (Q - 1)) :
    exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1 / 4 : ℝ)) ∧
    ∀ j : ℕ, 1 ≤ j → ∃ hx' : x ∈ (polynomialRoot (L := L) j).domain,
      ‖polynomialRoot j ⟨x, hx'⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2) := by
  have hExp := prop023_weak hK x hx hv hQ hN
  exact ⟨hExp, fun j hj => Prop023SpectralMoments.norm_of_exponential x Q hQ hExp j hj⟩

end QuantumNLS.Prop023Number
#print axioms QuantumNLS.Prop023Number.summable_normSq
#print axioms QuantumNLS.Prop023Number.sector_prob
#print axioms QuantumNLS.Prop023Number.odd_zero
#print axioms QuantumNLS.Prop023Number.prop023_weak
#print axioms QuantumNLS.Prop023Number.prop023_weak_moments
