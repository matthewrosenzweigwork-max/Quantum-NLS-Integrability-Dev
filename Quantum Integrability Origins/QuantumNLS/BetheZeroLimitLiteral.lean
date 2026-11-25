import Mathlib
import QuantumNLS.BetheZeroLimit

/-!
# R-CD2257D0 (`basis:lem:zero`): the first limit by the printed route

Source: `source/chapters/foundations/periodic_basis.tex` lines 164–180 (statement) and 174–191 (proof).
The printed first limit is proved here step by step, as printed:

1. (printed lines 175–181) `Y_c → Y_0` uniformly on compact subsets of `ℝⁿ`, with
   `Y_c(q) = (L/2)|q|² − 2π⟨I,q⟩ + 2∑_{j<k}∫_0^{q_j−q_k} arctan(s/c) ds` (accepted `yangYang`) and
   `Y_0(q) = (L/2)|q|² − 2π⟨I,q⟩ + π∑_{j<k}|q_j−q_k|`. The integrands are bounded by `π/2`; the error is
   controlled by dominated convergence (§1, §2, §4).
2. (printed lines 181–188) the minimum of `Y_0` is `q_0 = 2π(I−ρ)/L = 2πn/L`: a permutation sorting `q`
   decreasingly lowers `Y_0` (rearrangement, §8), and on the closed chamber `∑_{j<k}(q_j−q_k) = 2⟨ρ,q⟩`
   (§6, §7, §9).
3. (printed lines 189–190) strict convexity of `Y_0` makes its minimizer unique (§10, §11).
4. (printed lines 189–191) the bound `|q(n,c)| ≤ 2π|I|/L` (accepted `sourceRoots_norm_bound`), uniform
   convergence on compacts, and strict convexity identify every accumulation point of `q(n,c)` with `q_0`
   (§13). The minimality of `q(n,c)` for `Y_c` is the printed critical-point statement of `basis:lem:roots`
   (printed proof, line 143: "the equations are the critical-point equations of `Y_c`", whose unique
   critical point is its global minimum), accepted as `BetheConvexity.solution_isMin`.

The second limit is the accepted rho-weighted proof, `BetheZeroLimit.zero_limit_root` part 2, which
follows printed lines 193–203. The full lemma is `zero_limit_literal` (§14).

Accepted inputs (read-only): `BetheRoots.yangYang`, `pairPrimitive` (with evenness and zero value),
`BetheConvexity.solution_isMin`, `BetheConvexity.source_roots_spec`, `BetheSmooth.sourceRoots_norm_bound`,
`BetheZeroLimit.zrho`, `zsg`, `sum_zsg`, `zsg_neg`, `zsg_self`, `BetheZeroLimit.zero_limit_root`.
-/

namespace QuantumNLS.BetheZeroLimitLiteral

open Real Finset Filter Topology MeasureTheory
open QuantumNLS.BetheRoots (pairPrimitive pairPrimitive_even pairPrimitive_zero yangYang)
open QuantumNLS.BetheAdmission (logMap)
open QuantumNLS.BetheSmooth (sourceRoots sourceNumbers sourceRoots_norm_bound)
open QuantumNLS.BetheConvexity (solution_isMin source_roots_spec)
open QuantumNLS.BetheZeroLimit (zrho zsg sum_zsg zsg_neg zsg_self)

/-! ## 1. The dominating function (printed: integrands bounded by `π/2`) -/

/-- `F_c(s) = π/2 − arctan(s/c)` is strictly positive. -/
lemma F_pos (c s : ℝ) : 0 < π / 2 - arctan (s / c) := by
  have := arctan_lt_pi_div_two (s / c)
  linarith

/-- `F_c(s) ≤ π`. -/
lemma F_le_pi (c s : ℝ) : π / 2 - arctan (s / c) ≤ π := by
  have := neg_pi_div_two_lt_arctan (s / c)
  linarith

/-- Dominated convergence (printed: "dominated convergence"): `∫_0^R F_c → 0` as `c ↓ 0`, for `R ≥ 0`. -/
lemma tendsto_F_integral {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun c : ℝ => ∫ s in (0 : ℝ)..R, (π / 2 - arctan (s / c))) (𝓝[>] 0) (𝓝 0) := by
  have hcont : ∀ c : ℝ, Continuous (fun s : ℝ => π / 2 - arctan (s / c)) := by
    intro c; fun_prop
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ)) (a := 0) (b := R) (f := fun _ => (0 : ℝ))
    (F := fun c s => π / 2 - arctan (s / c)) (fun _ => π)
    (Eventually.of_forall fun c => (hcont c).aestronglyMeasurable)
    (by
      filter_upwards with c
      exact ae_of_all _ fun s _ => by
        rw [Real.norm_eq_abs, abs_of_pos (F_pos c s)]
        exact F_le_pi c s)
    intervalIntegrable_const
    (ae_of_all _ fun s hs => by
      rw [Set.uIoc_of_le hR] at hs
      have hs0 : 0 < s := hs.1
      have hinv : Tendsto (fun c : ℝ => s / c) (𝓝[>] 0) atTop := by
        simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hs0
      have harc : Tendsto (fun c : ℝ => arctan (s / c)) (𝓝[>] 0) (𝓝 (π / 2)) := by
        have h1 : Tendsto arctan atTop (𝓝 (π / 2)) :=
          (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1
        exact h1.comp hinv
      have := (tendsto_const_nhds (x := π / 2)).sub harc
      simpa using this)
  simpa using h

/-! ## 2. Error of the pair primitive (printed: integral error at the endpoint) -/

/-- For `0 ≤ d ≤ R`: `|pp_c(d) − (π/2)d| ≤ ∫_0^R F_c`. -/
lemma pp_error_nonneg {c : ℝ} (hc : 0 < c) {R d : ℝ} (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hdR : d ≤ R) :
    |(pairPrimitive c d - (π / 2) * |d|)| ≤ ∫ s in (0 : ℝ)..R, (π / 2 - arctan (s / c)) := by
  have hcont : Continuous (fun s : ℝ => π / 2 - arctan (s / c)) := by fun_prop
  have hi : IntervalIntegrable (fun s : ℝ => arctan (s / c)) volume 0 d :=
    (by fun_prop : Continuous (fun s : ℝ => arctan (s / c))).intervalIntegrable _ _
  have hint : (∫ s in (0 : ℝ)..d, (π / 2 - arctan (s / c))) = π / 2 * d - pairPrimitive c d := by
    unfold pairPrimitive
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hpos : 0 ≤ ∫ s in (0 : ℝ)..d, (π / 2 - arctan (s / c)) :=
    intervalIntegral.integral_nonneg hd0 (fun s _ => (F_pos c s).le)
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 R)] (fun s : ℝ => π / 2 - arctan (s / c)) :=
    ae_restrict_of_ae (ae_of_all _ fun s => (F_pos c s).le)
  have hmono : (∫ s in (0 : ℝ)..d, (π / 2 - arctan (s / c)))
      ≤ ∫ s in (0 : ℝ)..R, (π / 2 - arctan (s / c)) :=
    intervalIntegral.integral_mono_interval (le_refl 0) hd0 hdR hae (hcont.intervalIntegrable _ _)
  have e : pairPrimitive c d - (π / 2) * |d| = -(∫ s in (0 : ℝ)..d, (π / 2 - arctan (s / c))) := by
    rw [abs_of_nonneg hd0, hint]
    ring
  rw [e, abs_neg, abs_of_nonneg hpos]
  exact hmono

/-- Two-sided version, using evenness of the pair primitive (accepted `pairPrimitive_even`). -/
lemma pp_error_bound {c : ℝ} (hc : 0 < c) {R d : ℝ} (hR : 0 ≤ R) (hd : |d| ≤ R) :
    |(pairPrimitive c d - (π / 2) * |d|)| ≤ ∫ s in (0 : ℝ)..R, (π / 2 - arctan (s / c)) := by
  rcases le_total 0 d with hd0 | hd0
  · exact pp_error_nonneg hc hR hd0 ((le_abs_self d).trans hd)
  · have hnd : 0 ≤ -d := by linarith
    have hd1 : -d ≤ R := (neg_le_abs d).trans hd
    have h := pp_error_nonneg hc hR hnd hd1
    rw [pairPrimitive_even, abs_neg] at h
    exact h

/-! ## 3. Symmetric double sums (printed: pairs `j < k`) -/

/-- For a symmetric function with zero diagonal, `∑_{i,j} f = 2∑_{i<j} f`. -/
lemma sum_pairs_symm {N : ℕ} (f : Fin N → Fin N → ℝ) (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by
  have h1 : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, lt_asymm h]
    · simp [hdiag]
    · simp [h, lt_asymm h]
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm]
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by
        rw [h2]; ring

/-! ## 4. The literal functionals `Y_0` and the difference `Y_c − Y_0` -/

/-- The printed limit functional `Y_0(q) = (L/2)|q|² − ∑ b_i q_i + π∑_{j<k}|q_j−q_k|`, with `b = 2πI`. -/
noncomputable def Y0 {N : ℕ} (L : ℝ) (b q : Fin N → ℝ) : ℝ :=
  (∑ i, (L / 2 * q i ^ 2 - b i * q i)) + π * ∑ j, ∑ k, (if j < k then |q j - q k| else 0)

/-- `Y_c − Y_0 = 2∑_{j<k} (pp_c(q_j−q_k) − (π/2)|q_j−q_k|)`, the printed uniform-convergence error. -/
lemma yangYang_sub_Y0 {N : ℕ} (L c : ℝ) (b q : Fin N → ℝ) :
    yangYang L c b q - Y0 L b q
      = 2 * ∑ j, ∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0) := by
  have hsym := sum_pairs_symm (fun i j => pairPrimitive c (q i - q j))
    (fun i j => by
      show pairPrimitive c (q i - q j) = pairPrimitive c (q j - q i)
      rw [show q j - q i = -(q i - q j) by ring, pairPrimitive_even])
    (fun i => by
      show pairPrimitive c (q i - q i) = 0
      rw [sub_self, pairPrimitive_zero])
  have hterm : ∀ j k : Fin N,
      (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)
        = (if j < k then pairPrimitive c (q j - q k) else 0)
          - (π / 2) * (if j < k then |q j - q k| else 0) := by
    intro j k
    split_ifs <;> ring
  unfold yangYang Y0
  rw [hsym]
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `|Y_c(q) − Y_0(q)| ≤ 2N²δ` as soon as every pair error is at most `δ`. -/
lemma yangYang_Y0_abs_le {N : ℕ} {L c δ : ℝ} (b q : Fin N → ℝ) (hδ : 0 ≤ δ)
    (h : ∀ j k : Fin N, |(pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|)| ≤ δ) :
    |yangYang L c b q - Y0 L b q| ≤ 2 * ((N : ℝ) * N) * δ := by
  rw [yangYang_sub_Y0]
  have hsum : |∑ j, ∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)|
      ≤ ∑ j : Fin N, ∑ k : Fin N, δ := by
    calc |∑ j, ∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)|
        ≤ ∑ j, |∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ k, |if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0| :=
          Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ j : Fin N, ∑ k : Fin N, δ :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => by
            split_ifs with hjk
            · exact h j k
            · simp [hδ]))
  calc |2 * ∑ j, ∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)|
      = 2 * |∑ j, ∑ k, (if j < k then (pairPrimitive c (q j - q k) - (π / 2) * |q j - q k|) else 0)| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * ∑ j : Fin N, ∑ k : Fin N, δ := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * ((N : ℝ) * N) * δ := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

/-! ## 5. Labels, forcing and the zero-coupling vector -/

/-- Forcing `b_i = 2π(n_i + ρ_i)` (= `2π·sourceNumbers n i`). -/
noncomputable def bvec {N : ℕ} (n : Fin N → ℝ) : Fin N → ℝ := fun i => 2 * π * (n i + zrho N i)

/-- `q_0 = (2π/L) n`, the printed `q(n,0)`. -/
noncomputable def q0vec {N : ℕ} (L : ℝ) (n : Fin N → ℝ) : Fin N → ℝ := fun i => 2 * π / L * n i

lemma zrho_anti (N : ℕ) : Antitone (zrho N) := by
  intro i j hij
  unfold zrho
  have h : (i.val : ℝ) ≤ j.val := by exact_mod_cast (Fin.le_def.mp hij)
  linarith

lemma bvec_anti {N : ℕ} {n : Fin N → ℝ} (hn : ∀ i j : Fin N, i < j → n j ≤ n i) :
    Antitone (bvec n) := by
  intro i j hij
  unfold bvec
  have h1 : zrho N j ≤ zrho N i := zrho_anti N hij
  have h2 : n j ≤ n i := by
    rcases lt_or_eq_of_le hij with h | h
    · exact hn i j h
    · rw [h]
  have hpi : 0 < 2 * π := by positivity
  nlinarith

lemma q0vec_anti {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℝ}
    (hn : ∀ i j : Fin N, i < j → n j ≤ n i) : Antitone (q0vec L n) := by
  intro i j hij
  unfold q0vec
  have hcoef : 0 < 2 * π / L := by positivity
  rcases lt_or_eq_of_le hij with h | h
  · exact mul_le_mul_of_nonneg_left (hn i j h) hcoef.le
  · rw [h]

/-! ## 6. The antitone chamber: `∑_{j<k} |r_j − r_k| = 2⟨ρ, r⟩` (printed) -/

/-- For decreasing `r`: `∑_{j<k}|r_j−r_k| = 2∑_i ρ_i r_i`. -/
lemma pair_abs_antitone {N : ℕ} (r : Fin N → ℝ) (hr : Antitone r) :
    ∑ j, ∑ k, (if j < k then |r j - r k| else 0) = 2 * ∑ i, zrho N i * r i := by
  have hpt : ∀ j k : Fin N, (if j < k then |r j - r k| else 0)
      = (if j < k then (zsg j k * (r j - r k)) else 0) := by
    intro j k
    split_ifs with h
    · have hrk : r k ≤ r j := hr h.le
      have hz : zsg j k = 1 := by simp [zsg, h]
      rw [hz, one_mul, abs_of_nonneg (by linarith)]
    · rfl
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => hpt j k))]
  have hsym := sum_pairs_symm (fun j k => zsg j k * (r j - r k))
    (fun j k => by
      show zsg j k * (r j - r k) = zsg k j * (r k - r j)
      rw [zsg_neg]; ring)
    (fun j => by
      show zsg j j * (r j - r j) = 0
      rw [zsg_self]; ring)
  have hcol : ∀ k : Fin N, ∑ j, zsg j k = -(2 * zrho N k) := by
    intro k
    rw [Finset.sum_congr rfl (fun j _ => zsg_neg k j), Finset.sum_neg_distrib, sum_zsg]
  have hA : ∑ j, ∑ k, zsg j k * (r j - r k)
      = ∑ j, ∑ k, zsg j k * r j - ∑ j, ∑ k, zsg j k * r k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hB1 : ∑ j, ∑ k, zsg j k * r j = 2 * ∑ i, zrho N i * r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_mul, sum_zsg]; ring
  have hB2 : ∑ j, ∑ k, zsg j k * r k = ∑ k, (-(2 * zrho N k)) * r k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_mul, hcol k]
  have hneg : ∑ k, (-(2 * zrho N k)) * r k = -(2 * ∑ i, zrho N i * r i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hcomp : ∑ j, ∑ k, zsg j k * (r j - r k) = 4 * ∑ i, zrho N i * r i := by
    rw [hA, hB1, hB2, hneg]; ring
  linarith [hsym, hcomp]

/-! ## 7. `Y_0` on the chamber: `Y_0(r) = (L/2)|r − q_0|² − (L/2)|q_0|²` -/

lemma Y0_antitone {N : ℕ} {L : ℝ} (hL : L ≠ 0) {n : Fin N → ℝ}
    (r : Fin N → ℝ) (hr : Antitone r) :
    Y0 L (bvec n) r = (∑ i, L / 2 * (r i - q0vec L n i) ^ 2) - ∑ i, L / 2 * (q0vec L n i) ^ 2 := by
  unfold Y0
  rw [pair_abs_antitone r hr]
  have hq0 : ∀ i, L * q0vec L n i = 2 * π * n i := by
    intro i; unfold q0vec; field_simp
  have key : ∀ i, (L / 2 * (r i - q0vec L n i) ^ 2 - L / 2 * (q0vec L n i) ^ 2)
      = (L / 2 * r i ^ 2 - bvec n i * r i) + π * (2 * (zrho N i * r i)) := by
    intro i
    unfold bvec
    linear_combination (-(r i)) * hq0 i
  have hs : ∑ i, π * (2 * (zrho N i * r i)) = π * (2 * ∑ i, zrho N i * r i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp only [key]
  rw [Finset.sum_add_distrib, hs]

lemma Y0_q0 {N : ℕ} {L : ℝ} (hL : L ≠ 0) {n : Fin N → ℝ} (hn : ∀ i j : Fin N, i < j → n j ≤ n i)
    (hL0 : 0 < L) :
    Y0 L (bvec n) (q0vec L n) = -∑ i, L / 2 * (q0vec L n i) ^ 2 := by
  rw [Y0_antitone hL (q0vec L n) (q0vec_anti hL0 hn)]
  simp

/-! ## 8. Rearrangement: a permutation sorting `q` decreasingly lowers `Y_0` (printed) -/

lemma Y0_perm_le {N : ℕ} {L : ℝ} {b : Fin N → ℝ} (hb : Antitone b) (q : Fin N → ℝ) :
    ∃ r : Fin N → ℝ, Antitone r ∧ Y0 L b r ≤ Y0 L b q := by
  let σ : Equiv.Perm (Fin N) := Tuple.sort (fun i => -q i)
  have hmon := Tuple.monotone_sort (fun i => -q i)
  have hr : Antitone (fun i => q (σ i)) := by
    intro i j hij
    have := hmon hij
    simp only [Function.comp] at this
    show q (σ j) ≤ q (σ i)
    linarith
  refine ⟨fun i => q (σ i), hr, ?_⟩
  have hmv : Monovary b (fun i => q (σ i)) := hb.monovary hr
  have hlin : ∑ i, b i * q i ≤ ∑ i, b i * q (σ i) := by
    have := hmv.sum_smul_comp_perm_le_sum_smul (σ := σ.symm)
    simpa [smul_eq_mul] using this
  have hq2 : ∑ i, L / 2 * (q (σ i)) ^ 2 = ∑ i, L / 2 * q i ^ 2 :=
    Equiv.sum_comp σ (fun i => L / 2 * q i ^ 2)
  have hpair_abs : ∑ j, ∑ k, |q (σ j) - q (σ k)| = ∑ j, ∑ k, |q j - q k| := by
    calc ∑ j, ∑ k, |q (σ j) - q (σ k)|
        = ∑ j, ∑ k, |q (σ j) - q k| :=
          Finset.sum_congr rfl (fun j _ => Equiv.sum_comp σ (fun k => |q (σ j) - q k|))
      _ = ∑ j, ∑ k, |q j - q k| := Equiv.sum_comp σ (fun j => ∑ k, |q j - q k|)
  have e1 : ∑ j, ∑ k, |q (σ j) - q (σ k)|
      = 2 * ∑ j, ∑ k, (if j < k then |q (σ j) - q (σ k)| else 0) :=
    sum_pairs_symm (fun j k => |q (σ j) - q (σ k)|)
      (fun j k => by rw [abs_sub_comm])
      (fun j => by simp)
  have e2 : ∑ j, ∑ k, |q j - q k| = 2 * ∑ j, ∑ k, (if j < k then |q j - q k| else 0) :=
    sum_pairs_symm (fun j k => |q j - q k|)
      (fun j k => by rw [abs_sub_comm])
      (fun j => by simp)
  have hP : ∑ j, ∑ k, (if j < k then |q (σ j) - q (σ k)| else 0)
      = ∑ j, ∑ k, (if j < k then |q j - q k| else 0) := by linarith
  have hY : Y0 L b (fun i => q (σ i))
      = (∑ i, (L / 2 * (q (σ i)) ^ 2 - b i * q (σ i)))
        + π * ∑ j, ∑ k, (if j < k then |q (σ j) - q (σ k)| else 0) := rfl
  have hYq : Y0 L b q
      = (∑ i, (L / 2 * q i ^ 2 - b i * q i)) + π * ∑ j, ∑ k, (if j < k then |q j - q k| else 0) := rfl
  rw [hY, hYq, hP]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith [hq2, hlin]

/-- **Minimum of `Y_0` (printed: "the unique minimum is `q_0`").** `q_0` minimizes `Y_0` on `ℝⁿ`. -/
lemma Y0_min {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℝ}
    (hn : ∀ i j : Fin N, i < j → n j ≤ n i) (q : Fin N → ℝ) :
    Y0 L (bvec n) (q0vec L n) ≤ Y0 L (bvec n) q := by
  obtain ⟨r, hr, hle⟩ := Y0_perm_le (L := L) (bvec_anti hn) q
  have h1 := Y0_antitone (n := n) hL.ne' r hr
  have h3 : 0 ≤ ∑ i, L / 2 * (r i - q0vec L n i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (by linarith) (sq_nonneg _))
  have h2 := Y0_q0 hL.ne' hn hL
  linarith [h1, h2, h3, hle]

/-! ## 9. Midpoint inequality (printed: strict convexity of `Y_0`) -/

lemma Y0_mid {N : ℕ} (L : ℝ) (b y z : Fin N → ℝ) :
    Y0 L b (fun i => (y i + z i) / 2)
      ≤ (Y0 L b y + Y0 L b z) / 2 - L / 8 * ∑ i, (y i - z i) ^ 2 := by
  have hquad : ∀ i, (L / 2 * ((y i + z i) / 2) ^ 2 - b i * ((y i + z i) / 2))
      = (1 / 2) * (L / 2 * y i ^ 2 - b i * y i) + (1 / 2) * (L / 2 * z i ^ 2 - b i * z i)
          - L / 8 * (y i - z i) ^ 2 := by
    intro i; ring
  have hpair : ∀ j k : Fin N, (if j < k then |(y j + z j) / 2 - (y k + z k) / 2| else 0)
      ≤ (1 / 2) * (if j < k then |y j - y k| else 0) + (1 / 2) * (if j < k then |z j - z k| else 0) := by
    intro j k
    split_ifs with h
    · have e : (y j + z j) / 2 - (y k + z k) / 2 = ((y j - y k) + (z j - z k)) / 2 := by ring
      rw [e, abs_div, abs_two]
      linarith [abs_add_le (y j - y k) (z j - z k)]
    · simp
  have hq : ∑ i, (L / 2 * ((y i + z i) / 2) ^ 2 - b i * ((y i + z i) / 2))
      = (1 / 2) * ∑ i, (L / 2 * y i ^ 2 - b i * y i) + (1 / 2) * ∑ i, (L / 2 * z i ^ 2 - b i * z i)
          - L / 8 * ∑ i, (y i - z i) ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hquad i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hp : ∑ j, ∑ k, (if j < k then |(y j + z j) / 2 - (y k + z k) / 2| else 0)
      ≤ (1 / 2) * ∑ j, ∑ k, (if j < k then |y j - y k| else 0)
        + (1 / 2) * ∑ j, ∑ k, (if j < k then |z j - z k| else 0) := by
    calc ∑ j, ∑ k, (if j < k then |(y j + z j) / 2 - (y k + z k) / 2| else 0)
        ≤ ∑ j, ∑ k, ((1 / 2) * (if j < k then |y j - y k| else 0)
            + (1 / 2) * (if j < k then |z j - z k| else 0)) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hpair j k))
      _ = (1 / 2) * ∑ j, ∑ k, (if j < k then |y j - y k| else 0)
            + (1 / 2) * ∑ j, ∑ k, (if j < k then |z j - z k| else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hpi : 0 ≤ π := Real.pi_pos.le
  have hpm := mul_le_mul_of_nonneg_left hp hpi
  unfold Y0
  rw [hq]
  linarith [hpm]

/-! ## 10. Uniqueness of the minimizer (printed: strict convexity) -/

lemma Y0_unique {N : ℕ} {L : ℝ} (hL : 0 < L) {b q0 : Fin N → ℝ}
    (hmin : ∀ q, Y0 L b q0 ≤ Y0 L b q) (y : Fin N → ℝ) (hy : Y0 L b y ≤ Y0 L b q0) : y = q0 := by
  have hm := hmin (fun i => (y i + q0 i) / 2)
  have hmid := Y0_mid L b y q0
  have hS0 : 0 ≤ ∑ i, (y i - q0 i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hSpos : L / 8 * ∑ i, (y i - q0 i) ^ 2 ≤ 0 := by linarith
  have h8 : 0 < L / 8 := by linarith
  have hS' : ∑ i, (y i - q0 i) ^ 2 ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos h8 hcon
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i - q0 i))).mp
    (le_antisymm hS' hS0)
  funext i
  have h0 : (y i - q0 i) ^ 2 = 0 := hz i (mem_univ i)
  have h1 : y i - q0 i = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
  linarith

/-! ## 11. Continuity of `Y_0` -/

lemma Y0_continuous {N : ℕ} (L : ℝ) (b : Fin N → ℝ) : Continuous (Y0 L b) := by
  unfold Y0
  apply Continuous.add
  · fun_prop
  · apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro k _
    by_cases h : j < k
    · simp only [h, ite_true]
      fun_prop
    · simp only [h, ite_false]
      exact continuous_const

/-! ## 12. The printed first limit -/

/-- **Printed first limit (`basis:lem:zero`, line 166–168):** `q(n,c) → q(n,0) = (2π/L) n` as `c ↓ 0`, by
uniform convergence of `Y_c → Y_0` on compacts, the minimum of `Y_0` at `q_0`, its uniqueness by strict
convexity, the accepted bound and minimality of the roots. -/
theorem first_limit_literal {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℤ} (hn : Antitone n) :
    Tendsto (fun c => sourceRoots L n c) (𝓝[>] 0) (𝓝 (fun i => 2 * π / L * (n i : ℝ))) := by
  obtain ⟨nR, hnRdef⟩ : ∃ nR : Fin N → ℝ, nR = fun i => (n i : ℝ) := ⟨_, rfl⟩
  have hnRanti : ∀ i j : Fin N, i < j → nR j ≤ nR i := by
    intro i j h
    rw [hnRdef]
    exact Int.cast_le.mpr (hn h.le)
  have hgoal : (fun i => 2 * π / L * (n i : ℝ)) = q0vec L nR := by
    rw [hnRdef]; rfl
  rw [hgoal]
  -- the roots solve the printed equation with forcing `b = bvec nR` (accepted `source_roots_spec`)
  have hsr_eq : ∀ c : ℝ, 0 < c → logMap L c (sourceRoots L n c) = bvec nR := by
    intro c hc
    rw [((source_roots_spec hL hn).2 c hc).1]
    funext i
    rw [hnRdef]
    simp only [bvec, sourceNumbers, zrho]
    ring
  -- minimality of the roots for `Y_c` (accepted `solution_isMin`; printed critical-point statement)
  have hmin_c : ∀ c : ℝ, 0 < c → ∀ r : Fin N → ℝ,
      yangYang L c (bvec nR) (sourceRoots L n c) ≤ yangYang L c (bvec nR) r :=
    fun c hc => solution_isMin hL hc (hsr_eq c hc)
  -- the compact ball (printed: bound `|q| ≤ 2π|I|/L`, accepted `sourceRoots_norm_bound`)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ,
      R = 2 * π * Real.sqrt (∑ i, (sourceNumbers n i) ^ 2) / L + ‖q0vec L nR‖ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have : 0 ≤ 2 * π * Real.sqrt (∑ i, (sourceNumbers n i) ^ 2) / L :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg _)) hL.le
    linarith [norm_nonneg (q0vec L nR)]
  have hsr : ∀ c : ℝ, 0 < c → ‖sourceRoots L n c‖ ≤ R := by
    intro c hc
    refine (pi_norm_le_iff_of_nonneg hR0).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    have h1 : sourceRoots L n c i ^ 2 ≤ ∑ k, sourceRoots L n c k ^ 2 :=
      Finset.single_le_sum (f := fun k => sourceRoots L n c k ^ 2) (fun k _ => sq_nonneg _)
        (mem_univ i)
    have h2 := Real.abs_le_sqrt h1
    have h3 := sourceRoots_norm_bound hL hc n
    have h4 : 0 ≤ ‖q0vec L nR‖ := norm_nonneg _
    linarith
  have hq0R : ‖q0vec L nR‖ ≤ R := by
    rw [hRdef]
    have : 0 ≤ 2 * π * Real.sqrt (∑ i, (sourceNumbers n i) ^ 2) / L :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg _)) hL.le
    linarith
  -- printed uniform convergence `Y_c → Y_0` on the ball
  have hunif : ∀ ε > 0, ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ q : Fin N → ℝ, ‖q‖ ≤ R →
      |yangYang L c (bvec nR) q - Y0 L (bvec nR) q| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 * ((N : ℝ) * N) + 1) := ⟨_, rfl⟩
    have hD : 0 < 2 * ((N : ℝ) * N) + 1 := by positivity
    have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hε hD
    filter_upwards [(tendsto_F_integral (R := 2 * R) (by linarith)).eventually (gt_mem_nhds hδpos),
      self_mem_nhdsWithin] with c hG hc
    have hcpos : 0 < c := hc
    intro q hq
    refine (yangYang_Y0_abs_le (c := c) (bvec nR) q hδpos.le ?_).trans ?_
    · intro j k
      have hbd : ∀ l : Fin N, |q l| ≤ R := fun l => by
        have := norm_le_pi_norm q l
        rw [Real.norm_eq_abs] at this
        linarith
      have hjk : |q j - q k| ≤ 2 * R := by
        have := abs_sub (q j) (q k)
        linarith [hbd j, hbd k]
      exact (pp_error_bound hcpos (by linarith) hjk).trans hG.le
    · have hle : 2 * ((N : ℝ) * N) * δ ≤ ε := by
        rw [hδdef, mul_div_assoc', div_le_iff₀ hD]
        nlinarith
      exact hle
  -- printed bound: at any `c`, `Y_0(q(n,c)) ≤ Y_0(q_0) + 2ε`
  have hY0 : ∀ ε > 0, ∀ᶠ c in 𝓝[>] (0 : ℝ),
      Y0 L (bvec nR) (sourceRoots L n c) ≤ Y0 L (bvec nR) (q0vec L nR) + 2 * ε := by
    intro ε hε
    filter_upwards [hunif ε hε, self_mem_nhdsWithin] with c hU hc
    have hcpos : 0 < c := hc
    have h1 := hU (sourceRoots L n c) (hsr c hcpos)
    have h2 := hU (q0vec L nR) hq0R
    have h3 := hmin_c c hcpos (q0vec L nR)
    rw [abs_le] at h1 h2
    linarith [h1.1, h2.2, h3]
  have hsub : ∀ᶠ c in 𝓝[>] (0 : ℝ), sourceRoots L n c ∈ Metric.closedBall (0 : Fin N → ℝ) R := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact mem_closedBall_zero_iff.mpr (hsr c hc)
  refine IsCompact.tendsto_nhds_of_unique_mapClusterPt (isCompact_closedBall 0 R) hsub ?_
  intro x _ hx
  -- every accumulation point minimizes `Y_0` (printed), hence equals `q_0` by uniqueness
  have hle : Y0 L (bvec nR) x ≤ Y0 L (bvec nR) (q0vec L nR) := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨m, hm⟩ : ∃ m, m = Y0 L (bvec nR) (q0vec L nR) := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = (Y0 L (bvec nR) x + m) / 2 := ⟨_, rfl⟩
    have hmt : m < t := by rw [ht]; linarith
    have hte : t < Y0 L (bvec nR) x := by rw [ht]; linarith
    have hfreq : ∃ᶠ c in 𝓝[>] (0 : ℝ), t < Y0 L (bvec nR) (sourceRoots L n c) :=
      hx.frequently (p := fun y => t < Y0 L (bvec nR) y)
        (((Y0_continuous L (bvec nR)).tendsto x).eventually (lt_mem_nhds hte))
    have hlt : ∀ᶠ c in 𝓝[>] (0 : ℝ), Y0 L (bvec nR) (sourceRoots L n c) < t := by
      filter_upwards [hY0 ((t - m) / 4) (by linarith)] with c hc
      rw [← hm] at hc
      linarith
    obtain ⟨c, hc1, hc2⟩ := (hfreq.and_eventually hlt).exists
    linarith
  exact Y0_unique hL (Y0_min hL hnRanti) x hle

/-! ## 13. The full lemma -/

/-- **R-CD2257D0 (`basis:lem:zero`), full statement, first limit by the printed route.**
For each fixed label `n` (antitone, `n ∈ 𝔑_N`) and `L > 0`:
(1) `q(n,c) → q(n,0) = (2π/L) n` as `c ↓ 0` (printed route, `first_limit_literal`);
(2) `(q_i(n,c) − q_j(n,c))/c → +∞` for `i < j`, including `n_i = n_j` (accepted rho-weighted proof,
`BetheZeroLimit.zero_limit_root` part 2). -/
theorem zero_limit_literal {N : ℕ} {L : ℝ} (hL : 0 < L) {n : Fin N → ℤ} (hn : Antitone n) :
    Tendsto (fun c => sourceRoots L n c) (𝓝[>] 0) (𝓝 (fun i => 2 * π / L * (n i : ℝ))) ∧
    ∀ i j : Fin N, i < j →
      Tendsto (fun c => (sourceRoots L n c i - sourceRoots L n c j) / c) (𝓝[>] 0) atTop :=
  ⟨first_limit_literal hL hn, (QuantumNLS.BetheZeroLimit.zero_limit_root hL hn).2⟩

end QuantumNLS.BetheZeroLimitLiteral

#print axioms QuantumNLS.BetheZeroLimitLiteral.first_limit_literal
#print axioms QuantumNLS.BetheZeroLimitLiteral.zero_limit_literal
