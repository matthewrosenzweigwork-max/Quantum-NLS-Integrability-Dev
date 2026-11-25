import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST055
import NlsGge.Atomic.KST.KST056
import NlsGge.Atomic.KST.KST057

set_option autoImplicit false

open Filter
open scoped BigOperators ENNReal Topology

namespace NlsGge.Atomic.KST

noncomputable section

/-- The source auxiliary weight, with its zero mode defined separately. -/
def dyadicAuxiliaryWeight (c : ℕ → ℝ) (k : ℤ) : ℝ :=
  if k = 0 then 1 else 1 + dyadicMinorant c k.natAbs

@[simp] theorem dyadicAuxiliaryWeight_zero (c : ℕ → ℝ) :
    dyadicAuxiliaryWeight c 0 = 1 := by
  simp [dyadicAuxiliaryWeight]

theorem dyadicAuxiliaryWeight_of_ne_zero (c : ℕ → ℝ) {k : ℤ} (hk : k ≠ 0) :
    dyadicAuxiliaryWeight c k = 1 + dyadicMinorant c k.natAbs := by
  simp [dyadicAuxiliaryWeight, hk]

theorem dyadicAuxiliaryWeight_even (c : ℕ → ℝ) (k : ℤ) :
    dyadicAuxiliaryWeight c (-k) = dyadicAuxiliaryWeight c k := by
  by_cases hk : k = 0
  · simp [hk, dyadicAuxiliaryWeight]
  · rw [dyadicAuxiliaryWeight_of_ne_zero c (neg_ne_zero.mpr hk),
      dyadicAuxiliaryWeight_of_ne_zero c hk, Int.natAbs_neg]

private lemma dyadicAuxiliaryWeight_pow_two {w : ℤ → ℝ}
    (hw : SlowWeight w 2) (m : ℕ) :
    w ((2 ^ m : ℕ) : ℤ) ≤ (2 ^ m : ℝ) * w 1 := by
  induction m with
  | zero => simpa using (le_rfl : w 1 ≤ w 1)
  | succ m ih =>
      have hindex : ((2 ^ (m + 1) : ℕ) : ℤ) = 2 * ((2 ^ m : ℕ) : ℤ) := by
        push_cast
        change 2 ^ Nat.succ m = 2 * 2 ^ m
        rw [pow_succ]
        ring
      rw [hindex]
      calc
        w (2 * ((2 ^ m : ℕ) : ℤ)) ≤ 2 * w ((2 ^ m : ℕ) : ℤ) := hw.doubling _
        _ ≤ 2 * ((2 ^ m : ℝ) * w 1) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 ^ (m + 1) : ℝ) * w 1 := by push_cast; ring

private lemma finite_support_pair_weighted_summable {x : ℤ → ℂ}
    (hfin : (Function.support x).Finite) :
    Summable (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hpos : ({n : ℕ | x (n : ℤ) ≠ 0}).Finite :=
    Set.Finite.preimage (f := fun n : ℕ => (n : ℤ))
      (by intro a ha b hb hab; exact Int.ofNat_injective hab) hfin
  have hneg : ({n : ℕ | x (-(n : ℤ)) ≠ 0}).Finite :=
    Set.Finite.preimage (f := fun n : ℕ => -(n : ℤ))
      (by intro a ha b hb hab; exact Int.ofNat_injective (neg_injective hab)) hfin
  have hterms : (Function.support (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2)).Finite := by
    apply (hpos.union hneg).subset
    intro n hn
    have hterm : (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) *
        ((n + 1 : ℕ) : ℝ) ^ 2 ≠ 0 := by
      simpa only [Function.mem_support] using hn
    have hcoord : x (n : ℤ) ≠ 0 ∨ x (-(n : ℤ)) ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h.1, h.2] at hterm
    exact hcoord
  exact summable_of_finite_support hterms

private lemma dyadicAuxiliaryWeight_weighted_summable
    {x : ℤ → ℂ} {c : ℕ → ℝ}
    (hx : Memℓp x 2)
    (hdpos : ∀ n, 1 ≤ n → 0 < dyadicMinorant c n)
    (hcdom : ∀ n, 1 ≤ n → dyadicMinorant c n ≤ c n)
    (hcSum : Summable (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2)) :
    Summable (fun k : ℤ => ‖x k‖ ^ 2 * dyadicAuxiliaryWeight c k ^ 2) := by
  have hsq : Summable (fun k : ℤ => ‖x k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hx.summable (by norm_num)
  have hpairShift : Summable (fun n : ℕ =>
      (‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 + ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2) * c (n + 1) ^ 2) :=
    (summable_nat_add_iff 1).2 hcSum
  let g : ℤ → ℝ := fun k => if k = 0 then 0 else ‖x k‖ ^ 2 * c k.natAbs ^ 2
  have hposRay : Summable (fun n : ℕ => g ((n + 1 : ℕ) : ℤ)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hpairShift
    have hn0 : ((n + 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hle : ‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 * c (n + 1) ^ 2 ≤
        (‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2) * c (n + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)
    change (if ((n + 1 : ℕ) : ℤ) = 0 then 0 else
      ‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 *
        c (((n + 1 : ℕ) : ℤ).natAbs) ^ 2) ≤ _
    rw [if_neg hn0, Int.natAbs_natCast]
    exact hle
  have hnegRay : Summable (fun n : ℕ => g (-((n + 1 : ℕ) : ℤ))) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hpairShift
    have hn0 : -((n + 1 : ℕ) : ℤ) ≠ 0 := by
      exact neg_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero n))
    have hle : ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2 * c (n + 1) ^ 2 ≤
        (‖x ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2) * c (n + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
    change (if -((n + 1 : ℕ) : ℤ) = 0 then 0 else
      ‖x (-((n + 1 : ℕ) : ℤ))‖ ^ 2 *
        c (-((n + 1 : ℕ) : ℤ)).natAbs ^ 2) ≤ _
    rw [if_neg hn0, Int.natAbs_neg, Int.natAbs_natCast]
    exact hle
  have hg : Summable g := Summable.of_add_one_of_neg_add_one hposRay hnegRay
  have hmajor : ∀ k : ℤ,
      ‖x k‖ ^ 2 * dyadicAuxiliaryWeight c k ^ 2 ≤ 2 * ‖x k‖ ^ 2 + 2 * g k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [dyadicAuxiliaryWeight, g]
      nlinarith [sq_nonneg ‖x 0‖]
    · have hn : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
      rw [dyadicAuxiliaryWeight_of_ne_zero c hk]
      have hdc : dyadicMinorant c k.natAbs ≤ c k.natAbs := hcdom _ hn
      have hdnonneg : 0 ≤ dyadicMinorant c k.natAbs := (hdpos k.natAbs hn).le
      have hweight : (1 + dyadicMinorant c k.natAbs) ^ 2 ≤
          2 + 2 * c k.natAbs ^ 2 := by
        nlinarith [sq_nonneg (c k.natAbs - 1)]
      have hxnonneg : 0 ≤ ‖x k‖ ^ 2 := sq_nonneg _
      have hgk : g k = ‖x k‖ ^ 2 * c k.natAbs ^ 2 := by simp [g, hk]
      rw [hgk]
      calc
        ‖x k‖ ^ 2 * (1 + dyadicMinorant c k.natAbs) ^ 2 ≤
            ‖x k‖ ^ 2 * (2 + 2 * c k.natAbs ^ 2) :=
              mul_le_mul_of_nonneg_left hweight hxnonneg
        _ = 2 * ‖x k‖ ^ 2 + 2 * (‖x k‖ ^ 2 * c k.natAbs ^ 2) := by ring
  have hsumMajor : Summable (fun k : ℤ => 2 * ‖x k‖ ^ 2 + 2 * g k) :=
    (hsq.mul_left 2).add (hg.mul_left 2)
  exact Summable.of_nonneg_of_le (fun k => by positivity) hmajor hsumMajor

/-- Properties of the literal auxiliary weight built from the KST dyadic
minorant. -/
theorem dyadicAuxiliaryWeight_spec (x : ℤ → ℂ) (c : ℕ → ℝ)
    (hx : Memℓp x 2)
    (hpos : ∀ n, 1 ≤ n → 0 < c n)
    (hmono : MonotoneOn c (Set.Ici 1))
    (hcTendsto : Tendsto c atTop atTop)
    (hcSum : Summable (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2)) :
    SlowWeight (dyadicAuxiliaryWeight c) 2 ∧
    Tendsto (fun n : ℕ => dyadicAuxiliaryWeight c (n : ℤ)) atTop atTop ∧
    Summable (fun k : ℤ => ‖x k‖ ^ 2 * dyadicAuxiliaryWeight c k ^ 2) ∧
    (∀ k : ℤ, k ≠ 0 →
      dyadicAuxiliaryWeight c k ≤
        2 * dyadicAuxiliaryWeight c 1 * (k.natAbs : ℝ)) := by
  have hprops := dyadicMinorant_properties c hpos hmono
  have hdpos := hprops.1
  have hdmono := hprops.2.1
  have hddom := hprops.2.2.1
  have hdrec := hprops.2.2.2
  have hdT := dyadicMinorant_tendsto_atTop c hpos hmono hcTendsto
  let w := dyadicAuxiliaryWeight c
  have hwzero : w 0 = 1 := by simp [w]
  have hwne {k : ℤ} (hk : k ≠ 0) : w k = 1 + dyadicMinorant c k.natAbs :=
    dyadicAuxiliaryWeight_of_ne_zero c hk
  have hwone : ∀ k : ℤ, 1 ≤ w k := by
    intro k
    by_cases hk : k = 0
    · simp [w, hk]
    · rw [hwne hk]
      have hn : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk
      linarith [hdpos k.natAbs hn]
  have hweven (k : ℤ) : w (-k) = w k := by
    simpa [w] using dyadicAuxiliaryWeight_even c k
  have hwradial : ∀ a b : ℤ, a.natAbs ≤ b.natAbs → w a ≤ w b := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      exact hwone b
    · have hb : b ≠ 0 := by
        intro hb
        subst b
        have : 0 < a.natAbs := Int.natAbs_pos.mpr ha
        omega
      have ha1 : 1 ≤ a.natAbs := Int.natAbs_pos.mpr ha
      have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb
      rw [hwne ha, hwne hb]
      have hdle := hdmono (by simp; exact ha1) (by simp; exact hb1) hab
      nlinarith [hdle]
  have hwdoubling (k : ℤ) : w (2 * k) ≤ 2 * w k := by
    by_cases hk : k = 0
    · subst k
      norm_num [w]
    · have h2k : 2 * k ≠ 0 := mul_ne_zero (by norm_num) hk
      rw [hwne h2k, hwne hk, Int.natAbs_mul]
      have hrec := hdrec k.natAbs (Int.natAbs_pos.mpr hk)
      have hdn : 0 ≤ dyadicMinorant c k.natAbs :=
        (hdpos k.natAbs (Int.natAbs_pos.mpr hk)).le
      have : 1 + dyadicMinorant c (2 * k.natAbs) ≤
          2 * (1 + dyadicMinorant c k.natAbs) := by nlinarith [hrec, hdn]
      simpa using this
  have hwslow : SlowWeight w 2 := ⟨hwone, hweven, hwradial, hwdoubling⟩
  have hwT : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop := by
    have hplus : Tendsto (fun n : ℕ => 1 + dyadicMinorant c n) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [(Filter.tendsto_atTop.1 hdT) (b - 1)] with n hn
      linarith
    have hEq : (fun n : ℕ => w (n : ℤ)) =ᶠ[atTop]
        fun n : ℕ => 1 + dyadicMinorant c n := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hcast : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
      change dyadicAuxiliaryWeight c (n : ℤ) = 1 + dyadicMinorant c n
      rw [dyadicAuxiliaryWeight_of_ne_zero c hcast, Int.natAbs_natCast]
    exact hplus.congr' hEq.symm
  have hwsum : Summable (fun k : ℤ => ‖x k‖ ^ 2 * w k ^ 2) := by
    dsimp [w]
    exact dyadicAuxiliaryWeight_weighted_summable hx hdpos hddom hcSum
  have hlinear : ∀ k : ℤ, k ≠ 0 → w k ≤ 2 * w 1 * (k.natAbs : ℝ) := by
    intro k hk
    let n := k.natAbs
    have hn : 0 < n := Int.natAbs_pos.mpr hk
    let m := (Nat.log 2 n).succ
    have hlow : n ≤ 2 ^ m := by
      dsimp [m]
      exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    have hhighNat : 2 ^ m ≤ 2 * n := by
      dsimp [m]
      rw [Nat.pow_succ]
      calc
        2 ^ Nat.log 2 n * 2 ≤ n * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hn.ne')
        _ = 2 * n := by omega
    have harg1 : k.natAbs ≤ ((n : ℤ).natAbs) := by
      change n ≤ n
      rfl
    have harg2 : (n : ℤ).natAbs ≤ ((2 ^ m : ℕ) : ℤ).natAbs := by
      simp only [Int.natAbs_natCast]
      exact hlow
    have hkPow : w k ≤ w ((2 ^ m : ℕ) : ℤ) :=
      (hwradial k (n : ℤ) harg1).trans (hwradial (n : ℤ) ((2 ^ m : ℕ) : ℤ) harg2)
    have hpow := dyadicAuxiliaryWeight_pow_two hwslow m
    have hw1nonneg : 0 ≤ w 1 := le_trans (by norm_num) (hwone 1)
    calc
      w k ≤ w ((2 ^ m : ℕ) : ℤ) := hkPow
      _ ≤ (2 ^ m : ℝ) * w 1 := hpow
      _ ≤ (2 * n : ℝ) * w 1 := by
        apply mul_le_mul_of_nonneg_right _ hw1nonneg
        exact_mod_cast hhighNat
      _ = 2 * w 1 * (k.natAbs : ℝ) := by dsimp [n]; ring
  exact ⟨hwslow, hwT, hwsum, hlinear⟩

private lemma finiteSupport_multiplier_summable {x : ℤ → ℂ}
    (hx : Memℓp x 2) (hfin : (Function.support x).Finite) :
    Summable (fun n : ℕ =>
      (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * ((n + 1 : ℕ) : ℝ) ^ 2) :=
  finite_support_pair_weighted_summable hfin

/-- Every square-summable complex sequence admits the literal KST auxiliary
weight. The zero mode is one; all nonzero modes are one plus the dyadic
minorant evaluated at the integer absolute value. -/
theorem auxiliaryWeight_exists {x : ℤ → ℂ} (hx : Memℓp x 2) :
    ∃ c : ℕ → ℝ,
      (∀ n, 1 ≤ n → 0 < c n) ∧
      MonotoneOn c (Set.Ici 1) ∧
      Tendsto c atTop atTop ∧
      Summable (fun n : ℕ =>
        (‖x (n : ℤ)‖ ^ 2 + ‖x (-(n : ℤ))‖ ^ 2) * c n ^ 2) ∧
      SlowWeight (dyadicAuxiliaryWeight c) 2 ∧
      dyadicAuxiliaryWeight c 0 = 1 ∧
      Tendsto (fun n : ℕ => dyadicAuxiliaryWeight c (n : ℤ)) atTop atTop ∧
      Summable (fun k : ℤ => ‖x k‖ ^ 2 * dyadicAuxiliaryWeight c k ^ 2) ∧
      (∀ k : ℤ, k ≠ 0 →
        dyadicAuxiliaryWeight c k ≤
          2 * dyadicAuxiliaryWeight c 1 * (k.natAbs : ℝ)) := by
  classical
  by_cases hfin : (Function.support x).Finite
  · let c : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
    have hpos : ∀ n, 1 ≤ n → 0 < c n := by
      intro n hn
      dsimp [c]
      positivity
    have hmono : Monotone c := by
      intro m n hmn
      dsimp [c]
      exact_mod_cast (Nat.add_le_add_right hmn 1)
    have htend : Tendsto c atTop atTop := by
      dsimp [c]
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hsum := finiteSupport_multiplier_summable hx hfin
    have hmonoOn : MonotoneOn c (Set.Ici 1) := by
      intro a ha b hb hab
      exact hmono hab
    have hspec := dyadicAuxiliaryWeight_spec x c hx hpos hmonoOn htend hsum
    exact ⟨c, hpos, hmonoOn, htend, hsum, hspec.1, by simp [dyadicAuxiliaryWeight],
      hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩
  · obtain ⟨c, hmono, htend, hEanti, hEzero, hEpos, hformula, hsum, hbound⟩ :=
      exists_tail_multiplier_infinite hx hfin
    have hpos : ∀ n, 1 ≤ n → 0 < c n := by
      intro n hn
      rw [hformula n (by omega)]
      exact inv_pos.mpr (Real.sqrt_pos.2 (hEpos n (by omega)))
    have hmonoOn : MonotoneOn c (Set.Ici 1) := by
      intro a ha b hb hab
      exact hmono hab
    have hspec := dyadicAuxiliaryWeight_spec x c hx hpos hmonoOn htend hsum
    exact ⟨c, hpos, hmonoOn, htend, hsum, hspec.1,
      by simp [dyadicAuxiliaryWeight], hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩

end
end NlsGge.Atomic.KST
