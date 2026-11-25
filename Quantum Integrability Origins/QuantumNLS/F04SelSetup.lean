import QuantumNLS.F02FiniteGap
import QuantumNLS.F04SelRank

/-! R-F4C3E5BE CC:F04:selection (root_response/F04.tex:202), stage S1: the finite setup of the
printed proof.  For old occupations `eta` with `eta_b >= 1` and `m = eta - e_b + e_a`, `b < a`,
a threshold `k in [b, a)`:
* `rk`: the forced rank `i_N = C_{k,N}` (zero-based index, `rk_val`);
* `rk_labels`: `b <= d_N <= k < e_N <= a` for `d_N = n_{i_N}`, `e_N = ~n_{i_N}`;
* `sParam_spec`: for `lambda in (k, k+1)` the parameter `s_N(lambda) = (lambda - d_N)/(e_N - d_N)`
  lies in `(0,1)` and the selected real label is exactly `lambda`;
* `other_labels`: `nu_j(s) <= k` for `j < i_N` and `>= k+1` for `j > i_N` (printed `CC:F04:other-labels`);
* `qPath_realBethe`: for `s in [0,1]` the path roots solve the printed `CC:F04:real-bethe` (the
  `LocalHeight.RealBethe` structure with `c_N = kappa/N`);
* `path_mono`, `path_l1`: `q(0) <= q(s) <= q(1)` and `sum_j |q_j(s) - q_j(1)| = 2 pi (a-b)(1-s)/L`
  (printed `CC:F04:path-distance`);
* `weakConv_of_l1`, `path_weak`: the empirical measures along `s_N in [0,1]` have the same weak
  limit as an endpoint (Lipschitz test functions, `O(1/N)` mean displacement). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.F04SelSetup

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.AdjacentResponse
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.RootDisplacement
open QuantumNLS.OrderedResponse QuantumNLS.RootContraction QuantumNLS.F02FiniteGap
open QuantumNLS.Ext025A6 (realLabelForce f02_roots_joint_analyticAt f02_roots_solve)
open QuantumNLS.RootDisplacementEstimate (pair_identity count_erase)
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.LabelJointWeak

variable {N : ℕ}

/-! ### 1. The forced rank and its labels -/

theorem Ccum_pos (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {k : ℤ} (hk : b ≤ k) : 1 ≤ Ccum η k := by
  have := Ccum_jump η hk
  omega

/-- The forced rank `C_k` as a zero-based index. -/
def rk (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {k : ℤ} (hk : b ≤ k) : Fin N :=
  ⟨Ccum η k - 1, by have := Ccum_pos η hb hk; have := Ccum_le_N η k; omega⟩

theorem rk_val (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {k : ℤ} (hk : b ≤ k) :
    ((rk η hb hk).val : ℤ) + 1 = Ccum η k := by
  have := Ccum_pos η hb hk
  simp only [rk]
  omega

theorem rk_labels (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) :
    b ≤ labs η (rk η hb (Finset.mem_Ico.1 hk).1) ∧ labs η (rk η hb (Finset.mem_Ico.1 hk).1) ≤ k ∧
      k + 1 ≤ labs (transfer η hb a) (rk η hb (Finset.mem_Ico.1 hk).1) ∧
      labs (transfer η hb a) (rk η hb (Finset.mem_Ico.1 hk).1) ≤ a := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.1 hk
  have hv := rk_val η hb hbk
  obtain ⟨h1, h2, h3, h4⟩ := rank_labels η hb hab hk (rk η hb hbk) hv
  refine ⟨h1, ?_, ?_, h4⟩
  · exact (labs_le_iff η _ k).2 (by omega)
  · by_contra hcon
    push Not at hcon
    have h5 := (labs_le_iff (transfer η hb a) (rk η hb hbk) k).1 (by omega)
    have h6 := Ccum_transfer η hb a k
    rw [if_pos hbk, if_neg (by omega)] at h6
    omega

theorem labs_le_transfer (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) (i : Fin N) :
    labs η i ≤ labs (transfer η hb a) i := by
  have h := rankVec_eq η hb hab i
  have h0 := rankVec_nonneg η b a i
  have : (labs η i : ℝ) ≤ labs (transfer η hb a) i := by linarith
  exact_mod_cast this

theorem other_labels (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (j : Fin N) :
    (j < rk η hb (Finset.mem_Ico.1 hk).1 → nuPath η hb a s j ≤ k) ∧
    (rk η hb (Finset.mem_Ico.1 hk).1 < j → (k : ℝ) + 1 ≤ nuPath η hb a s j) := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.1 hk
  have hv := rk_val η hb hbk
  have hle : (labs η j : ℝ) ≤ labs (transfer η hb a) j := by
    exact_mod_cast labs_le_transfer η hb hab j
  constructor
  · intro hj
    have hjv : (j.val : ℤ) < (rk η hb hbk).val := by exact_mod_cast hj
    have h5 := Ccum_transfer η hb a k
    rw [if_pos hbk, if_neg (by omega)] at h5
    have h6 : labs (transfer η hb a) j ≤ k := (labs_le_iff _ j k).2 (by omega)
    have h6' : (labs (transfer η hb a) j : ℝ) ≤ k := by exact_mod_cast h6
    unfold nuPath
    nlinarith
  · intro hj
    have hjv : (rk η hb hbk).val < j.val := by exact_mod_cast hj
    have h6 : k + 1 ≤ labs η j := by
      by_contra hcon
      have := (labs_le_iff η j k).1 (by omega)
      omega
    have h6' : ((k : ℝ) + 1) ≤ labs η j := by exact_mod_cast h6
    unfold nuPath
    nlinarith

/-- The printed parameter `s_N(lambda) = (lambda - d_N)/(e_N - d_N)`. -/
def sParam (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} {k : ℤ} (hk : b ≤ k) (lam : ℝ) : ℝ :=
  (lam - (labs η (rk η hb hk) : ℝ)) / ((labs (transfer η hb a) (rk η hb hk) : ℝ) - labs η (rk η hb hk))

theorem sParam_spec (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) {lam : ℝ} (hl1 : (k : ℝ) < lam) (hl2 : lam < (k : ℝ) + 1) :
    0 < sParam η hb (a := a) (Finset.mem_Ico.1 hk).1 lam ∧
    sParam η hb (a := a) (Finset.mem_Ico.1 hk).1 lam < 1 ∧
    nuPath η hb a (sParam η hb (a := a) (Finset.mem_Ico.1 hk).1 lam)
      (rk η hb (Finset.mem_Ico.1 hk).1) = lam := by
  obtain ⟨_, h2, h3, _⟩ := rk_labels η hb hab hk
  have h2' : (labs η (rk η hb (Finset.mem_Ico.1 hk).1) : ℝ) ≤ k := by exact_mod_cast h2
  have h3' : ((k : ℝ) + 1) ≤ labs (transfer η hb a) (rk η hb (Finset.mem_Ico.1 hk).1) := by
    exact_mod_cast h3
  set d : ℝ := (labs η (rk η hb (Finset.mem_Ico.1 hk).1) : ℝ) with hd
  set e : ℝ := (labs (transfer η hb a) (rk η hb (Finset.mem_Ico.1 hk).1) : ℝ) with he
  have hde : 0 < e - d := by linarith
  unfold sParam
  refine ⟨?_, ?_, ?_⟩
  · apply div_pos _ hde
    linarith
  · rw [div_lt_one hde]
    linarith
  · unfold nuPath
    simp only [← hd, ← he]
    field_simp
    ring

/-! ### 2. The path roots solve the printed real-label Bethe equations -/

theorem qPath_realBethe {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {n : ℕ} (η : MArr (n + 1)) {b : ℤ}
    (hb : 1 ≤ η.1 b) (a : ℤ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    RealBethe L κ n (qPath L (κ / ((n : ℝ) + 1)) η hb a s) (nuPath η hb a s) := by
  have hc : 0 < κ / ((n : ℝ) + 1) := by positivity
  have hν := nuPath_monotone η hb a h0 h1
  have hd := QuantumNLS.F02Round6Derivative.coupling_derivative hL hc hν
  dsimp only at hd
  obtain ⟨hq, -⟩ := hd
  set c := κ / ((n : ℝ) + 1) with hcdef
  set q := root L (realLabelForce (nuPath η hb a s)) c with hqdef
  refine ⟨hq, hν, fun i => ?_⟩
  have hpair : ∀ k ∈ Finset.univ.erase i,
      2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k)) =
        if k < i then Real.pi else -Real.pi := by
    intro k hk
    have hne : k ≠ i := Finset.ne_of_mem_erase hk
    have hx : q i - q k ≠ 0 := by
      intro e
      exact hne (hq.injective (sub_eq_zero.1 e)).symm
    rw [pair_identity hc hx]
    simp only [sub_pos, hq.lt_iff_lt]
  have hsplit : ∑ k ∈ Finset.univ.erase i,
      (2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k))) =
        ∑ k ∈ Finset.univ.erase i, (if k < i then Real.pi else -Real.pi) :=
    Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, count_erase] at hsplit
  have h1' := f02_roots_solve hL hc (nuPath η hb a s) i
  rw [← hqdef] at h1'
  push_cast at h1' hsplit
  change L * q i - 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (q i - q j)) =
    2 * Real.pi * nuPath η hb a s i
  linarith

/-! ### 3. Monotonicity in `s` and the exact displacement -/

theorem delta_nonneg (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) (i : Fin N) :
    0 ≤ labelIncrement (labs η) (labs (transfer η hb a)) i := by
  unfold labelIncrement
  have : (labs η i : ℝ) ≤ labs (transfer η hb a) i := by
    exact_mod_cast labs_le_transfer η hb hab i
  linarith

theorem delta_sum (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) :
    ∑ i, labelIncrement (labs η) (labs (transfer η hb a)) i = (a : ℝ) - b := by
  have h := sum_rankVec η hb hab
  have e : ∀ i, labelIncrement (labs η) (labs (transfer η hb a)) i = rankVec η b a i := by
    intro i
    rw [rankVec_eq η hb hab i]
    rfl
  simp_rw [e]
  rw [h]

variable {L c : ℝ}

theorem path_mono (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (j : Fin N) :
    qPath L c η hb a 0 j ≤ qPath L c η hb a s j ∧ qPath L c η hb a s j ≤ qPath L c η hb a 1 j := by
  rw [qPath_eq_frac]
  have hm : Monotone (fun t => fracRoots L c (realLabels (labs η))
      (labelIncrement (labs η) (labs (transfer η hb a))) t j) :=
    monotone_of_deriv_nonneg
      (fun t => (fracRoots_coord_hasDerivAt hL hc _ _ t j).differentiableAt)
      (fun t => by
        rw [(fracRoots_coord_hasDerivAt hL hc _ _ t j).deriv]
        exact fracRoots_deriv_nonneg hL hc _ _ (delta_nonneg η hb hab) t j)
  exact ⟨hm h0, hm h1⟩

theorem sum_path_sub (hL : 0 < L) (hc : 0 < c) (x δ : Fin N → ℝ) (s : ℝ) :
    ∑ j, (fracRoots L c x δ 1 j - fracRoots L c x δ s j) =
      2 * Real.pi / L * (∑ i, δ i) * (1 - s) := by
  have hG : ∀ s : ℝ, HasDerivAt
      (fun t => ∑ j, fracRoots L c x δ t j - 2 * Real.pi / L * (∑ i, δ i) * t) 0 s := by
    intro s
    have h1 : HasDerivAt (fun t => ∑ j, fracRoots L c x δ t j)
        (∑ j, deriv (fracRoots L c x δ) s j) s :=
      HasDerivAt.fun_sum (u := Finset.univ)
        (fun j _ => fracRoots_coord_hasDerivAt hL hc x δ s j)
    have h2 : HasDerivAt (fun t => (∑ j, fracRoots L c x δ t j) -
        2 * Real.pi / L * (∑ i, δ i) * t)
        ((∑ j, deriv (fracRoots L c x δ) s j) - 2 * Real.pi / L * (∑ i, δ i) * 1) s :=
      h1.sub ((hasDerivAt_id s).const_mul (2 * Real.pi / L * (∑ i, δ i)))
    convert h2 using 1
    rw [sum_deriv_fracRoots hL hc x δ s]
    ring
  have hconst : (∑ j, fracRoots L c x δ 1 j) - 2 * Real.pi / L * (∑ i, δ i) * 1 =
      (∑ j, fracRoots L c x δ s j) - 2 * Real.pi / L * (∑ i, δ i) * s :=
    is_const_of_deriv_eq_zero
      (fun s => (hG s).differentiableAt) (fun s => (hG s).deriv) 1 s
  rw [Finset.sum_sub_distrib]
  linarith

theorem path_l1 (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∑ j, |qPath L c η hb a s j - qPath L c η hb a 1 j| =
      2 * Real.pi * ((a : ℝ) - b) * (1 - s) / L := by
  have hs := sum_path_sub hL hc (realLabels (labs η))
    (labelIncrement (labs η) (labs (transfer η hb a))) s
  rw [delta_sum η hb hab] at hs
  rw [← qPath_eq_frac] at hs
  have : ∀ j, |qPath L c η hb a s j - qPath L c η hb a 1 j| =
      qPath L c η hb a 1 j - qPath L c η hb a s j := fun j => by
    rw [abs_sub_comm, abs_of_nonneg]
    linarith [(path_mono hL hc η hb hab h0 h1 j).2]
  simp_rw [this]
  rw [hs]
  ring

/-! ### 4. Weak limits are insensitive to `O(1/N)` mean displacement -/

theorem weakConv_of_l1 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {q p : (N : ℕ) → Fin (N + 1) → ℝ} (hq : EmpiricalWeakConv q μ)
    (hd : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, |p N j - q N j|) atTop (𝓝 0)) :
    EmpiricalWeakConv p μ := by
  apply tendsto_weakConv
  rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hfb ⟨Lip, hLip⟩
  have hq' := (MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.1
    (weakConv_tendsto hq)) f hfb ⟨Lip, hLip⟩
  refine hq'.congr_dist ?_
  have hdn : Tendsto (fun N : ℕ => (Lip : ℝ) * ((1 / ((N : ℝ) + 1)) * ∑ j, |p N j - q N j|))
      atTop (𝓝 0) := by simpa using hd.const_mul (Lip : ℝ)
  refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hdn
  change dist (∫ x, f x ∂(empP (q N) : Measure ℝ)) (∫ x, f x ∂(empP (p N) : Measure ℝ)) ≤ _
  rw [integral_empP, integral_empP, Real.dist_eq, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹)]
  have h1 : |∑ j, (f (q N j) - f (p N j))| ≤ ∑ j, (Lip : ℝ) * |p N j - q N j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have := hLip.dist_le_mul (q N j) (p N j)
    rw [Real.dist_eq, Real.dist_eq] at this
    rw [abs_sub_comm (p N j) (q N j)]
    exact this
  rw [← Finset.mul_sum] at h1
  calc ((N : ℝ) + 1)⁻¹ * |∑ j, (f (q N j) - f (p N j))|
      ≤ ((N : ℝ) + 1)⁻¹ * ((Lip : ℝ) * ∑ j, |p N j - q N j|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (Lip : ℝ) * ((1 / ((N : ℝ) + 1)) * ∑ j, |p N j - q N j|) := by
        rw [one_div]; ring

/-- The weak limit of the empirical measures of the path roots `q_N(s_N)`, `s_N in [0,1]`, is the
weak limit `mu` of any endpoint: here the `s = 0` endpoint (the roots of the old array); the other
endpoint follows with `s_N = 1`. -/
theorem path_weak {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℤ} (hab : b < a) (η : (n : ℕ) → MArr (n + 1)) (hb : ∀ n, 1 ≤ (η n).1 b)
    (hend : EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hb n) a 1) μ)
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) :
    EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hb n) a (s n)) μ := by
  refine weakConv_of_l1 hend ?_
  have hC : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * (2 * Real.pi * ((a : ℝ) - b) / L)) atTop
      (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 * Real.pi * ((a : ℝ) - b) / L)
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hC
  have hc : 0 < κ / ((N : ℝ) + 1) := by positivity
  have := path_l1 hL hc (η N) (hb N) hab (hs0 N) (hs1 N)
  rw [this]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hba : (0 : ℝ) ≤ (a : ℝ) - b := by
    have : (b : ℝ) < a := by exact_mod_cast hab
    linarith
  have := hs0 N
  have := hs1 N
  rw [div_le_div_iff_of_pos_right hL]
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hba) (hs0 N)]

end QuantumNLS.F04SelSetup
#print axioms QuantumNLS.F04SelSetup.rk_labels
#print axioms QuantumNLS.F04SelSetup.other_labels
#print axioms QuantumNLS.F04SelSetup.sParam_spec
#print axioms QuantumNLS.F04SelSetup.qPath_realBethe
#print axioms QuantumNLS.F04SelSetup.path_mono
#print axioms QuantumNLS.F04SelSetup.path_l1
#print axioms QuantumNLS.F04SelSetup.weakConv_of_l1
#print axioms QuantumNLS.F04SelSetup.path_weak
