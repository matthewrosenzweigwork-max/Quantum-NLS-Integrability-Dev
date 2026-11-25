import Mathlib
import QuantumNLS.Prop023ProductBounds

/-! PROP-023 `Q7B:lem:moments`, scalar stage.  Sector probabilities `p_n` obeying the trace
recurrence `2 n p_n = sum_{m=1}^n t_m p_{n-m}` with a nonnegative submultiplicative sequence `t`
(`t_{a+b} <= t_a t_b`) satisfy, for every `N`, `s >= 1` and `B (s-1) < 1` with `B` bounding the
partial sums of `t`,

  `sum_{n<=N} p_n s^n <= (sum_{n<=N} p_n) exp(-log(1 - B(s-1))/2)`.

The proof is the Riccati comparison `s D' <= D + D^2` for `D(s) = sum_k t_k s^k` (from
submultiplicativity): no eigenvalues, no determinants, no infinite series.  In particular, for
`Q >= 1`, `B = Q - 1` and `s = exp(1/(8Q))`, `sum_{n<=N} p_n exp(n/(8Q)) <= e^{1/4} sum_{n<=N} p_n`
(`exp_moment_partial`), which is the exponential moment of PROP-023. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Finset
namespace QuantumNLS.Prop023Scalar

/-! ### 1. Reindexing lemmas -/

def tri (N : ℕ) : Finset (ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1)).filter fun x => x.1 + x.2 ≤ N

lemma sum_antidiagonal_tri (N : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ n ∈ range (N + 1), ∑ x ∈ antidiagonal n, f x = ∑ x ∈ tri N, f x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 + x.2) (t := range (N + 1))
    (s := tri N)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := by simpa [Nat.lt_succ_iff] using hn
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [tri, mem_filter, mem_product, mem_range, HasAntidiagonal.mem_antidiagonal]
    constructor
    · intro h
      omega
    · rintro ⟨⟨h1, h2⟩, h4⟩
      omega
  · intro x hx
    simp only [tri, mem_filter, mem_product, mem_range] at hx
    simp only [mem_range]
    omega

lemma cauchy_le (N : ℕ) (u v : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) :
    ∑ n ∈ range (N + 1), ∑ x ∈ antidiagonal n, u x.1 * v x.2 ≤
      (∑ a ∈ range (N + 1), u a) * ∑ b ∈ range (N + 1), v b := by
  rw [sum_antidiagonal_tri, Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [tri, mem_filter] at hx
    exact hx.1
  · intro x _ _
    exact mul_nonneg (hu _) (hv _)

/-! ### 2. The Riccati inequality -/

structure SubMul (t : ℕ → ℝ) : Prop where
  zero : t 0 = 0
  nonneg : ∀ k, 0 ≤ t k
  submul : ∀ a b, 1 ≤ a → 1 ≤ b → t (a + b) ≤ t a * t b

lemma pair_lower {t : ℕ → ℝ} (h : SubMul t) {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) - 1) * t k ≤ ∑ x ∈ antidiagonal k, t x.1 * t x.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ a ∈ Ico 1 k, t k ≤ ∑ a ∈ range (k + 1), t a * t (k - a) := by
    calc ∑ a ∈ Ico 1 k, t k ≤ ∑ a ∈ Ico 1 k, t a * t (k - a) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_Ico] at ha
          have := h.submul a (k - a) ha.1 (by omega)
          rwa [show a + (k - a) = k by omega] at this
      _ ≤ ∑ a ∈ range (k + 1), t a * t (k - a) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            rw [Finset.mem_Ico] at ha
            rw [Finset.mem_range]; omega
          · intro a _ _
            exact mul_nonneg (h.nonneg _) (h.nonneg _)
  have h2 : ∑ a ∈ Ico 1 k, t k = ((k : ℝ) - 1) * t k := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [Nat.cast_sub hk]; simp
  linarith

lemma riccati {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∑ k ∈ range (M + 1), (k : ℝ) * t k * s ^ k ≤
      (∑ k ∈ range (M + 1), t k * s ^ k) + (∑ k ∈ range (M + 1), t k * s ^ k) ^ 2 := by
  set u : ℕ → ℝ := fun k => t k * s ^ k with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => mul_nonneg (h.nonneg k) (pow_nonneg hs k)
  have hc := cauchy_le M u u hu0 hu0
  have key : ∀ k ∈ range (M + 1), (k : ℝ) * t k * s ^ k ≤
      u k + ∑ x ∈ antidiagonal k, u x.1 * u x.2 := by
    intro k _
    by_cases hk : k = 0
    · subst hk; simp [hu, h.zero]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hp := pair_lower h hk1
      have e : ∑ x ∈ antidiagonal k, u x.1 * u x.2 =
          (∑ x ∈ antidiagonal k, t x.1 * t x.2) * s ^ k := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [HasAntidiagonal.mem_antidiagonal] at hx
        simp only [hu]
        rw [← hx, pow_add]; ring
      rw [e]
      have hsk : 0 ≤ s ^ k := pow_nonneg hs k
      have := mul_le_mul_of_nonneg_right hp hsk
      simp only [hu]
      nlinarith
  calc ∑ k ∈ range (M + 1), (k : ℝ) * t k * s ^ k
      ≤ ∑ k ∈ range (M + 1), (u k + ∑ x ∈ antidiagonal k, u x.1 * u x.2) :=
        Finset.sum_le_sum key
    _ = ∑ k ∈ range (M + 1), u k + ∑ k ∈ range (M + 1), ∑ x ∈ antidiagonal k, u x.1 * u x.2 :=
        Finset.sum_add_distrib
    _ ≤ _ := by
        rw [sq]
        exact add_le_add le_rfl hc

/-! ### 3. Calculus on the truncated sums -/

def DD (t : ℕ → ℝ) (M : ℕ) (s : ℝ) : ℝ := ∑ k ∈ range (M + 1), t k * s ^ k
def Dd (t : ℕ → ℝ) (M : ℕ) (s : ℝ) : ℝ := ∑ k ∈ range (M + 1), t k * ((k : ℝ) * s ^ (k - 1))

lemma hasDerivAt_DD (t : ℕ → ℝ) (M : ℕ) (s : ℝ) : HasDerivAt (DD t M) (Dd t M s) s := by
  unfold DD Dd
  apply HasDerivAt.fun_sum
  intro k _
  exact (hasDerivAt_pow k s).const_mul (t k)

lemma s_mul_Dd (t : ℕ → ℝ) (M : ℕ) (s : ℝ) :
    s * Dd t M s = ∑ k ∈ range (M + 1), (k : ℝ) * t k * s ^ k := by
  unfold Dd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : s * s ^ (k - 1) = s ^ k := by
      rw [← pow_succ']; congr 1; omega
    calc s * (t k * ((k : ℝ) * s ^ (k - 1))) = (k : ℝ) * t k * (s * s ^ (k - 1)) := by ring
      _ = _ := by rw [this]

lemma DD_nonneg {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ DD t M s :=
  Finset.sum_nonneg fun k _ => mul_nonneg (h.nonneg k) (pow_nonneg hs k)

lemma ratio_antitone {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) :
    AntitoneOn (fun s => DD t M s / (s * (1 + DD t M s))) (Set.Ici 1) := by
  have hpos : ∀ s : ℝ, 1 ≤ s → 0 < s * (1 + DD t M s) := fun s hs =>
    mul_pos (by linarith) (by linarith [DD_nonneg h M (by linarith : (0 : ℝ) ≤ s)])
  have hder : ∀ s : ℝ, 1 ≤ s → HasDerivAt (fun s => DD t M s / (s * (1 + DD t M s)))
      ((Dd t M s * (s * (1 + DD t M s)) - DD t M s * ((1 + DD t M s) + s * Dd t M s)) /
        (s * (1 + DD t M s)) ^ 2) s := by
    intro s hs
    have h1 := hasDerivAt_DD t M s
    have h2 : HasDerivAt (fun s => s * (1 + DD t M s)) ((1 + DD t M s) + s * Dd t M s) s := by
      have := (hasDerivAt_id' s).mul ((hasDerivAt_const s (1 : ℝ)).add h1)
      convert this using 1
      simp
    exact h1.div h2 (hpos s hs).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · intro s hs
    exact (hder s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact (hder s (le_of_lt hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs1 : 1 ≤ s := le_of_lt hs
    rw [(hder s hs1).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hr := riccati h M (by linarith : (0 : ℝ) ≤ s)
    rw [← s_mul_Dd] at hr
    unfold DD at *
    nlinarith

lemma DD_bound {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) {B : ℝ} (hB0 : 0 ≤ B) (hB : DD t M 1 ≤ B)
    {s : ℝ} (hs : 1 ≤ s) (hBs : B * (s - 1) < 1) :
    DD t M s ≤ s * B / (1 - B * (s - 1)) := by
  have hanti := ratio_antitone h M (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only at hanti
  have hD1 := DD_nonneg h M (by norm_num : (0 : ℝ) ≤ 1)
  have hDs := DD_nonneg h M (by linarith : (0 : ℝ) ≤ s)
  have h1 : DD t M 1 / (1 * (1 + DD t M 1)) ≤ B / (1 + B) := by
    rw [one_mul, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 := hanti.trans h1
  rw [div_le_div_iff₀ (by positivity) (by linarith)] at h2
  have hden : 0 < 1 - B * (s - 1) := by linarith
  rw [le_div_iff₀ hden]
  nlinarith

def Ph (t : ℕ → ℝ) (M : ℕ) (s : ℝ) : ℝ := ∑ k ∈ range (M + 1), t k * ((s ^ k - 1) / k)

lemma hasDerivAt_Ph (t : ℕ → ℝ) (M : ℕ) (s : ℝ) :
    HasDerivAt (Ph t M) (∑ k ∈ range (M + 1), t k * (((k : ℝ) * s ^ (k - 1)) / k)) s := by
  unfold Ph
  apply HasDerivAt.fun_sum
  intro k _
  exact (((hasDerivAt_pow k s).sub_const 1).div_const (k : ℝ)).const_mul (t k)

lemma s_mul_Ph' {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) (s : ℝ) :
    s * (∑ k ∈ range (M + 1), t k * (((k : ℝ) * s ^ (k - 1)) / k)) = DD t M s := by
  unfold DD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [h.zero]
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have : s * s ^ (k - 1) = s ^ k := by
      rw [← pow_succ']; congr 1; omega
    calc s * (t k * (((k : ℝ) * s ^ (k - 1)) / k)) = t k * (s * s ^ (k - 1)) := by
          field_simp
      _ = _ := by rw [this]

lemma Ph_le {t : ℕ → ℝ} (h : SubMul t) (M : ℕ) {B : ℝ} (hB0 : 0 ≤ B) (hB : DD t M 1 ≤ B)
    {s : ℝ} (hs : 1 ≤ s) (hBs : B * (s - 1) < 1) :
    Ph t M s ≤ -Real.log (1 - B * (s - 1)) := by
  set ψ : ℝ → ℝ := fun x => -Real.log (1 - B * (x - 1)) - Ph t M x with hψ
  have hpos : ∀ x ∈ Set.Icc 1 s, 0 < 1 - B * (x - 1) := by
    intro x hx
    have : B * (x - 1) ≤ B * (s - 1) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hB0
    linarith
  have hder : ∀ x ∈ Set.Icc 1 s, HasDerivAt ψ
      (B / (1 - B * (x - 1)) - ∑ k ∈ range (M + 1), t k * (((k : ℝ) * x ^ (k - 1)) / k)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 - B * (x - 1)) (-B) x := by
      have := ((hasDerivAt_id' x).sub_const 1).const_mul B
      simpa using this.const_sub 1
    have h2 := (h1.log (hpos x hx).ne').neg
    have h3 := h2.sub (hasDerivAt_Ph t M x)
    convert h3 using 1
    ring
  have hmono : MonotoneOn ψ (Set.Icc 1 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 s)
    · intro x hx; exact (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hder x (Set.Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Set.Ioo_subset_Icc_self hx
      rw [(hder x hx').deriv]
      have hxpos : 0 < x := by linarith [hx.1]
      have hDb := DD_bound h M hB0 hB (le_of_lt hx.1) (by
        have : B * (x - 1) ≤ B * (s - 1) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hB0
        linarith)
      have hden := hpos x hx'
      have hid := s_mul_Ph' h M x
      have hsum : ∑ k ∈ range (M + 1), t k * (((k : ℝ) * x ^ (k - 1)) / k) = DD t M x / x := by
        rw [eq_div_iff hxpos.ne', mul_comm]; exact hid
      rw [hsum]
      have : DD t M x / x ≤ B / (1 - B * (x - 1)) := by
        rw [div_le_iff₀ hxpos]
        calc DD t M x ≤ x * B / (1 - B * (x - 1)) := hDb
          _ = B / (1 - B * (x - 1)) * x := by ring
      linarith
  have h0 : ψ 1 = 0 := by simp [hψ, Ph]
  have := hmono (Set.left_mem_Icc.2 hs) (Set.right_mem_Icc.2 hs) hs
  rw [h0] at this
  simp only [hψ] at this
  linarith

/-! ### 4. The generating function -/

def FF (p : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℝ := ∑ n ∈ range (N + 1), p n * s ^ n
def Fd (p : ℕ → ℝ) (N : ℕ) (s : ℝ) : ℝ := ∑ n ∈ range (N + 1), p n * ((n : ℝ) * s ^ (n - 1))

lemma hasDerivAt_FF (p : ℕ → ℝ) (N : ℕ) (s : ℝ) : HasDerivAt (FF p N) (Fd p N s) s := by
  unfold FF Fd
  apply HasDerivAt.fun_sum
  intro n _
  exact (hasDerivAt_pow n s).const_mul (p n)

lemma s_mul_Fd (p : ℕ → ℝ) (N : ℕ) (s : ℝ) :
    s * Fd p N s = ∑ n ∈ range (N + 1), (n : ℝ) * p n * s ^ n := by
  unfold Fd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : s * s ^ (k - 1) = s ^ k := by
      rw [← pow_succ']; congr 1; omega
    calc s * (p k * ((k : ℝ) * s ^ (k - 1))) = (k : ℝ) * p k * (s * s ^ (k - 1)) := by ring
      _ = _ := by rw [this]

lemma FF_nonneg {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ FF p N s :=
  Finset.sum_nonneg fun n _ => mul_nonneg (hp n) (pow_nonneg hs n)

lemma FF_antitone {t p : ℕ → ℝ} (h : SubMul t) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n : ℕ, 2 * (n : ℝ) * p n = ∑ x ∈ antidiagonal n, t x.1 * p x.2) (N : ℕ) :
    AntitoneOn (fun s => FF p N s * Real.exp (-(Ph t N s) / 2)) (Set.Ici 1) := by
  have hder : ∀ s : ℝ, HasDerivAt (fun s => FF p N s * Real.exp (-(Ph t N s) / 2))
      (Fd p N s * Real.exp (-(Ph t N s) / 2) + FF p N s *
        (Real.exp (-(Ph t N s) / 2) *
          (-(∑ k ∈ range (N + 1), t k * (((k : ℝ) * s ^ (k - 1)) / k)) / 2))) s := by
    intro s
    have h1 := hasDerivAt_FF p N s
    have h2 := ((hasDerivAt_Ph t N s).neg.div_const 2).exp
    exact h1.mul h2
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · intro s hs; exact (hder s).continuousAt.continuousWithinAt
  · intro s hs; exact (hder s).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have hs1 : (0 : ℝ) < s := by have := Set.mem_Ioi.1 hs; linarith
    rw [(hder s).deriv]
    have hid := s_mul_Ph' h N s
    set E := Real.exp (-(Ph t N s) / 2) with hE
    set A := ∑ k ∈ range (N + 1), t k * (((k : ℝ) * s ^ (k - 1)) / k) with hA
    have hEpos : 0 < E := Real.exp_pos _
    have hsFd : s * Fd p N s ≤ DD t N s * FF p N s / 2 := by
      rw [s_mul_Fd]
      have hsum : ∑ n ∈ range (N + 1), (n : ℝ) * p n * s ^ n =
          (∑ n ∈ range (N + 1), ∑ x ∈ antidiagonal n,
            (t x.1 * s ^ x.1) * (p x.2 * s ^ x.2)) / 2 := by
        rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        have e1 : ∑ x ∈ antidiagonal n, (t x.1 * s ^ x.1) * (p x.2 * s ^ x.2) =
            (∑ x ∈ antidiagonal n, t x.1 * p x.2) * s ^ n := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [HasAntidiagonal.mem_antidiagonal] at hx
          rw [← hx, pow_add]; ring
        rw [e1, ← hrec n]; ring
      rw [hsum]
      have hc := cauchy_le N (fun k => t k * s ^ k) (fun n => p n * s ^ n)
        (fun k => mul_nonneg (h.nonneg k) (pow_nonneg hs1.le k))
        (fun n => mul_nonneg (hp n) (pow_nonneg hs1.le n))
      unfold DD FF
      linarith
    have hFnn := FF_nonneg hp N hs1.le
    have : Fd p N s * E + FF p N s * (E * (-A / 2)) = E * (Fd p N s - A * FF p N s / 2) := by ring
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos hEpos.le
    have hAs : A = DD t N s / s := by
      rw [eq_div_iff hs1.ne', mul_comm]; exact hid
    have h3 : Fd p N s ≤ DD t N s * FF p N s / (2 * s) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have : A * FF p N s / 2 = DD t N s * FF p N s / (2 * s) := by
      rw [hAs]; field_simp
    linarith

/-- **The generating-function bound.** -/
theorem gen_bound {t p : ℕ → ℝ} (h : SubMul t) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n : ℕ, 2 * (n : ℝ) * p n = ∑ x ∈ antidiagonal n, t x.1 * p x.2) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ M, ∑ k ∈ range (M + 1), t k ≤ B) {s : ℝ} (hs : 1 ≤ s)
    (hBs : B * (s - 1) < 1) (N : ℕ) :
    FF p N s ≤ FF p N 1 * Real.exp (-Real.log (1 - B * (s - 1)) / 2) := by
  have hanti := FF_antitone h hp hrec N (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only at hanti
  have hPh1 : Ph t N 1 = 0 := by unfold Ph; simp
  rw [hPh1] at hanti
  have hD1 : DD t N 1 ≤ B := by
    have := hB N
    unfold DD
    simpa using this
  have hPhle : Ph t N s ≤ -Real.log (1 - B * (s - 1)) := Ph_le h N hB0 hD1 hs hBs
  have hF1 : 0 ≤ FF p N 1 := FF_nonneg hp N (by norm_num)
  have h2 : FF p N s ≤ FF p N 1 * Real.exp (Ph t N s / 2) := by
    have h3 := mul_le_mul_of_nonneg_right hanti (Real.exp_pos (Ph t N s / 2)).le
    have e1 : FF p N s * Real.exp (-(Ph t N s) / 2) * Real.exp (Ph t N s / 2) = FF p N s := by
      rw [mul_assoc, ← Real.exp_add]
      have : -(Ph t N s) / 2 + Ph t N s / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    have e2 : FF p N 1 * Real.exp (-(0 : ℝ) / 2) = FF p N 1 := by simp
    rw [e1, e2] at h3
    exact h3
  calc FF p N s ≤ FF p N 1 * Real.exp (Ph t N s / 2) := h2
    _ ≤ FF p N 1 * Real.exp (-Real.log (1 - B * (s - 1)) / 2) := by
        apply mul_le_mul_of_nonneg_left _ hF1
        apply Real.exp_le_exp.2
        linarith

/-! ### 5. The exponential moment of PROP-023 -/

lemma neg_log_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) : -Real.log (1 - x) / 2 ≤ x := by
  have hp : 0 < 1 - x := by linarith
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hp)
  rw [Real.log_inv] at h1
  have h2 : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hp.ne', div_le_iff₀ hp]
    nlinarith
  linarith

/-- With `Q >= 1`, `B = Q - 1`, `s = exp(1/(8Q))`: `sum p_n exp(n/(8Q)) <= e^{1/4} sum p_n`
(partial sums). -/
theorem exp_moment_partial {t p : ℕ → ℝ} (h : SubMul t) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n : ℕ, 2 * (n : ℝ) * p n = ∑ x ∈ antidiagonal n, t x.1 * p x.2) {Q : ℝ}
    (hQ : 1 ≤ Q) (hB : ∀ M, ∑ k ∈ range (M + 1), t k ≤ Q - 1) (N : ℕ) :
    ∑ n ∈ range (N + 1), p n * Real.exp (1 / (8 * Q)) ^ n ≤
      Real.exp (1 / 4 : ℝ) * ∑ n ∈ range (N + 1), p n := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨he0, he1⟩ := QuantumNLS.Prop023ProductBounds.exponential_increment hQ
  set s : ℝ := Real.exp (1 / (8 * Q)) with hs
  have hs1 : 1 ≤ s := by linarith
  have hBs : (Q - 1) * (s - 1) ≤ 1 / 4 := by
    calc (Q - 1) * (s - 1) ≤ (Q - 1) * (1 / (4 * Q)) :=
          mul_le_mul_of_nonneg_left he1 (by linarith)
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hx0 : 0 ≤ (Q - 1) * (s - 1) := mul_nonneg (by linarith) he0
  have hg := gen_bound h hp hrec (B := Q - 1) (by linarith) hB hs1 (by linarith) N
  have hl := neg_log_le hx0 hBs
  have hF1 : FF p N 1 = ∑ n ∈ range (N + 1), p n := by unfold FF; simp
  have h3 : FF p N s ≤ FF p N 1 * Real.exp ((Q - 1) * (s - 1)) := by
    refine hg.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hl) (FF_nonneg hp N (by norm_num)))
  have h4 : Real.exp ((Q - 1) * (s - 1)) ≤ Real.exp (1 / 4 : ℝ) := Real.exp_le_exp.2 hBs
  have hF1n := FF_nonneg hp N (by norm_num : (0 : ℝ) ≤ 1)
  calc ∑ n ∈ range (N + 1), p n * s ^ n = FF p N s := rfl
    _ ≤ FF p N 1 * Real.exp ((Q - 1) * (s - 1)) := h3
    _ ≤ FF p N 1 * Real.exp (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left h4 hF1n
    _ = Real.exp (1 / 4 : ℝ) * ∑ n ∈ range (N + 1), p n := by rw [hF1]; ring

/-! ### 6. The partial sums of `t` are bounded by the mean number -/

theorem partial_t_le {t p : ℕ → ℝ} (h : SubMul t) (hp : ∀ n, 0 ≤ p n)
    (hrec : ∀ n : ℕ, 2 * (n : ℝ) * p n = ∑ x ∈ antidiagonal n, t x.1 * p x.2) {E : ℝ}
    (hE : ∀ N, ∑ n ∈ range (N + 1), 2 * (n : ℝ) * p n ≤ E)
    (htot : Filter.Tendsto (fun N => ∑ n ∈ range N, p n) Filter.atTop (nhds 1)) (M : ℕ) :
    ∑ k ∈ range (M + 1), t k ≤ E := by
  have hlim : Filter.Tendsto (fun N : ℕ => (∑ k ∈ range (M + 1), t k) *
      ∑ j ∈ range (N - M + 1), p j) Filter.atTop (nhds ((∑ k ∈ range (M + 1), t k) * 1)) := by
    have hc : Filter.Tendsto (fun N : ℕ => N - M + 1) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.2
      intro b
      exact ⟨b + M, fun N hN => by omega⟩
    exact (htot.comp hc).const_mul _
  rw [mul_one] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop M] with N hN
  calc (∑ k ∈ range (M + 1), t k) * ∑ j ∈ range (N - M + 1), p j
      = ∑ x ∈ range (M + 1) ×ˢ range (N - M + 1), t x.1 * p x.2 := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
    _ ≤ ∑ x ∈ tri N, t x.1 * p x.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [mem_product, mem_range] at hx
          simp only [tri, mem_filter, mem_product, mem_range]
          omega
        · intro x _ _
          exact mul_nonneg (h.nonneg _) (hp _)
    _ = ∑ n ∈ range (N + 1), ∑ x ∈ antidiagonal n, t x.1 * p x.2 :=
        (sum_antidiagonal_tri N _).symm
    _ = ∑ n ∈ range (N + 1), 2 * (n : ℝ) * p n :=
        Finset.sum_congr rfl fun n _ => (hrec n).symm
    _ ≤ E := hE N

end QuantumNLS.Prop023Scalar
#print axioms QuantumNLS.Prop023Scalar.gen_bound
#print axioms QuantumNLS.Prop023Scalar.exp_moment_partial
#print axioms QuantumNLS.Prop023Scalar.partial_t_le
