import Mathlib
import QuantumNLS.RootDisplacementEstimate

/-!
# R-2EF16A1A: separation of every on-shell configuration (`lem:EP-spacing`)

Source: `source/chapters/quantitative/static_plane_rates.tex`.
* lines 13--29: normalization `c = κ/N`, the defect `δ_c`, the pair sum `𝒟_N`, and the constants
  `a_* = √(κ²+8κ/L) − κ`, `C_pair = π²κ²/(18 a_*²)`, `C_δ = 1 + 2 C_pair`;
* lines 33--41: the statement (`eq:EP-spacing`) with the N = 1 clause;
* lines 43--86: the printed proof, reproduced in §§4--6 below.

Ordered on-shell configuration: source `static_finite_gap.tex` eq:E-onshell,
`L q_j = 2π n_j + 2 Σ_{ℓ≠j} arctan(κ/(N(q_j−q_ℓ)))`, with `q_1<⋯<q_N` and `n_1≤⋯≤n_N` integers.
`OrderedOnShell` is this literal form.

Convention bridge (proved here, not assumed): `ordered_onshell_iff_roots` identifies `OrderedOnShell` with
the accepted root vector `BetheSmooth.roots L n (κ/N)` (R-4C8D7C9E). The DEF-006 rapidity equation `RapidityEq`
with labels `quantumNumbers n` is the intermediate (`rapidity_of_printed`), using the `RootDisplacementEstimate`
pattern (`pair_identity`, `count_erase`, `bethe_printed`).

Read-only imports: `RootDisplacementEstimate` (3d427628, accepted) and through it `BetheLabels` (DEF-006),
`BetheConvexity`, `BetheSmooth`, `BetheRoots`, `BetheAdmission`. No frozen file is edited.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
open QuantumNLS.BetheLabels QuantumNLS.BetheAdmission
open QuantumNLS.RootDisplacementEstimate (pair_identity count_erase bethe_printed)

namespace QuantumNLS.OnShellSpacing

/-! ## 1. Constants, defect, pair sum, empirical measure, on-shell configurations -/

/-- `a_* = √(κ²+8κ/L) − κ` (source line 23). -/
def aStar (κ L : ℝ) : ℝ := Real.sqrt (κ ^ 2 + 8 * κ / L) - κ

/-- `C_pair = π² κ² / (18 a_*²)` (source line 24). -/
def Cpair (κ L : ℝ) : ℝ := Real.pi ^ 2 * κ ^ 2 / (18 * aStar κ L ^ 2)

/-- `C_δ = 1 + 2 C_pair` (source line 25). -/
def Cdelta (κ L : ℝ) : ℝ := 1 + 2 * Cpair κ L

/-- `δ_c(d) = 1 − arctan(c/d)/(c/d)` for `d ≠ 0`, `δ_c(0) = 1` (source eq:EP-defect). -/
def defect (c d : ℝ) : ℝ := if d = 0 then 1 else 1 - Real.arctan (c / d) / (c / d)

/-- `𝒟_N(q) = Σ_{j<k} δ_c(q_j − q_k)` (source eq:EP-defect). -/
def pairDefect {N : ℕ} (c : ℝ) (q : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, ∑ k : Fin N, if j < k then defect c (q j - q k) else 0

/-- The empirical measure `L_N = N⁻¹ Σ_j δ_{q_j}` of a configuration `q`. -/
def empMeasure (N : ℕ) (q : Fin N → ℝ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ j : Fin N, Measure.dirac (q j)

/-- Ordered on-shell configuration (source static_finite_gap eq:E-onshell; Bethe normalization of
model.tex eq:corrected): `q` strictly increasing, `n` nondecreasing integers, and
`L q_j = 2π n_j + 2 Σ_{ℓ≠j} arctan(κ/(N(q_j−q_ℓ)))`. -/
def OrderedOnShell {N : ℕ} (L κ : ℝ) (n : Fin N → ℤ) (q : Fin N → ℝ) : Prop :=
  StrictMono q ∧ Monotone n ∧
    ∀ j : Fin N, L * q j = 2 * Real.pi * (n j : ℝ) +
      2 * ∑ l ∈ Finset.univ.erase j, Real.arctan (κ / ((N : ℝ) * (q j - q l)))

/-- The ℕ-indexed extension of a `Fin N`-indexed vector (zero outside `range N`). -/
def Qd {N : ℕ} (q : Fin N → ℝ) (m : ℕ) : ℝ := if h : m < N then q ⟨m, h⟩ else 0

/-- The ℕ-indexed DEF-006 label `I_m = n_m + m − (N−1)/2` (zero outside `range N`). -/
def Idd {N : ℕ} (n : Fin N → ℤ) (m : ℕ) : ℝ :=
  if h : m < N then quantumNumbers n ⟨m, h⟩ else 0

theorem Qd_val {N : ℕ} (q : Fin N → ℝ) (k : Fin N) : Qd q (k : ℕ) = q k := by
  unfold Qd
  rw [dif_pos k.isLt]

theorem Qd_lt {N : ℕ} {q : Fin N → ℝ} (hq : StrictMono q) {t : ℕ} (ht : t + 1 < N) :
    Qd q t < Qd q (t + 1) := by
  unfold Qd
  rw [dif_pos (by omega : t < N), dif_pos ht]
  exact hq (Fin.mk_lt_mk.2 (Nat.lt_succ_self t))

theorem sum_fin_eq_range {N : ℕ} (q : Fin N → ℝ) (φ : ℝ → ℝ) :
    ∑ k : Fin N, φ (q k) = ∑ m ∈ Finset.range N, φ (Qd q m) := by
  calc ∑ k : Fin N, φ (q k) = ∑ k : Fin N, φ (Qd q (k : ℕ)) :=
        Finset.sum_congr rfl (fun k _ => by rw [Qd_val])
    _ = ∑ m ∈ Finset.range N, φ (Qd q m) := Fin.sum_univ_eq_sum_range (fun m => φ (Qd q m)) N

/-! ## 2. Calculus facts on `[0, ∞)` -/

theorem monotoneOn_Ici_of_hasDeriv {f f' : ℝ → ℝ} (hd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hnn : ∀ t, 0 < t → 0 ≤ f' t) : MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    exact (hd t (Set.mem_Ici.mp ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hd t (Set.mem_Ioi.mp ht).le).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    rw [(hd t ht'.le).deriv]
    exact hnn t ht'

theorem antitoneOn_Ici_of_hasDeriv {f f' : ℝ → ℝ} (hd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hnp : ∀ t, 0 < t → f' t ≤ 0) : AntitoneOn f (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t ht
    exact (hd t (Set.mem_Ici.mp ht)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hd t (Set.mem_Ioi.mp ht).le).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    rw [(hd t ht'.le).deriv]
    exact hnp t ht'

/-- `arctan` is concave on `[0, ∞)` (derivative `1/(1+x²)` is antitone there). -/
theorem arctan_concaveOn : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.arctan := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) Real.continuous_arctan.continuousOn
  · rw [interior_Ici]
    exact Real.differentiable_arctan.differentiableOn
  · rw [interior_Ici, Real.deriv_arctan]
    intro x hx y hy hxy
    have hx' : 0 < x := Set.mem_Ioi.mp hx
    have hy' : 0 < y := Set.mem_Ioi.mp hy
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
    show 1 / (1 + y ^ 2) ≤ 1 / (1 + x ^ 2)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem arctan_add_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.arctan A + Real.arctan B ≤ 2 * Real.arctan ((A + B) / 2) := by
  have h := arctan_concaveOn.2 (Set.mem_Ici.mpr hA) (Set.mem_Ici.mpr hB)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1 / 2 * A + 1 / 2 * B = (A + B) / 2 := by ring
  rw [e] at h
  linarith

theorem arctan_scale_le {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : 0 ≤ y) :
    s * Real.arctan y ≤ Real.arctan (s * y) := by
  have h := arctan_concaveOn.2 (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
    hs0 (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
  simp only [smul_eq_mul, Real.arctan_zero, mul_zero, add_zero] at h
  exact h

/-- `x/(1+x) ≤ arctan x` for `x ≥ 0` (used for the lower bound in the quadratic step). -/
theorem div_one_add_le_arctan {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ Real.arctan x := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => Real.arctan y - y / (1 + y))
      (1 / (1 + t ^ 2) - (1 * (1 + t) - t * 1) / (1 + t) ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => y / (1 + y)) ((1 * (1 + t) - t * 1) / (1 + t) ^ 2) t :=
      (hasDerivAt_id' t).div ((hasDerivAt_id' t).const_add 1)
        (by show (1 + t) ≠ 0; exact (by linarith : (0 : ℝ) < 1 + t).ne')
    exact (Real.hasDerivAt_arctan t).sub h1
  have hmono := monotoneOn_Ici_of_hasDeriv (f' := fun t : ℝ =>
      1 / (1 + t ^ 2) - (1 * (1 + t) - t * 1) / (1 + t) ^ 2) hd (fun t ht => by
    have e : (1 * (1 + t) - t * 1) / (1 + t) ^ 2 = 1 / (1 + t) ^ 2 := by ring
    rw [e]
    have hle : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    exact sub_nonneg.2 (one_div_le_one_div_of_le (by positivity) hle))
  have h0 : (fun y : ℝ => Real.arctan y - y / (1 + y)) 0 = 0 := by simp
  have h2 := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
  have h3 : (fun y : ℝ => Real.arctan y - y / (1 + y)) x = Real.arctan x - x / (1 + x) := rfl
  simp only at h2
  linarith

/-- `y − y³/3 ≤ arctan y` for `y ≥ 0`. -/
theorem arctan_ge_cubic {y : ℝ} (hy : 0 ≤ y) : y - y ^ 3 / 3 ≤ Real.arctan y := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ => Real.arctan s - s + s ^ 3 / 3)
      (1 / (1 + t ^ 2) - 1 + t ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).div_const 3
      convert h using 1
      norm_num
    exact ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id' t)).add h1
  have hmono := monotoneOn_Ici_of_hasDeriv (f' := fun t : ℝ => 1 / (1 + t ^ 2) - 1 + t ^ 2) hd
    (fun t _ => by
      have hne : (1 + t ^ 2) ≠ 0 := by positivity
      have e : 1 / (1 + t ^ 2) - 1 + t ^ 2 = t ^ 4 / (1 + t ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity)
  have h0 : (fun s : ℝ => Real.arctan s - s + s ^ 3 / 3) 0 = 0 := by simp
  have h2 := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hy) hy
  have h3 : (fun s : ℝ => Real.arctan s - s + s ^ 3 / 3) y = Real.arctan y - y + y ^ 3 / 3 := rfl
  simp only at h2
  linarith

/-- `1 − arctan y / y ≤ y²/3` for `y > 0`. -/
theorem one_sub_arctan_div_le {y : ℝ} (hy : 0 < y) : 1 - Real.arctan y / y ≤ y ^ 2 / 3 := by
  have h := arctan_ge_cubic hy.le
  have h2 : 1 - y ^ 2 / 3 ≤ Real.arctan y / y := by
    rw [le_div_iff₀ hy]
    nlinarith [h]
  linarith

/-! ## 3. The defect and the pair sum (source lines 15--19, 75--85) -/

theorem defect_neg (c d : ℝ) : defect c (-d) = defect c d := by
  unfold defect
  by_cases hd : d = 0
  · simp [hd]
  · have hnd : -d ≠ 0 := neg_ne_zero.mpr hd
    rw [if_neg hnd, if_neg hd, div_neg, Real.arctan_neg, neg_div_neg_eq]

/-- `δ_c(d) ≤ c²/(3d²)` for `d ≠ 0` (source line 75--78: `0 ≤ 1 − arctan x/x ≤ x²/3`). -/
theorem defect_le {c d : ℝ} (hc : 0 < c) (hd : d ≠ 0) :
    defect c d ≤ c ^ 2 / (3 * d ^ 2) := by
  unfold defect
  rw [if_neg hd]
  have hx : c / d ≠ 0 := div_ne_zero hc.ne' hd
  have hk : 1 - Real.arctan (c / d) / (c / d) ≤ (c / d) ^ 2 / 3 := by
    rcases lt_or_gt_of_ne hx with h | h
    · have hy : 0 < -(c / d) := by linarith
      have h1 := one_sub_arctan_div_le hy
      have e1 : Real.arctan (c / d) / (c / d) = Real.arctan (-(c / d)) / (-(c / d)) := by
        rw [Real.arctan_neg, neg_div_neg_eq]
      rw [e1]
      have e2 : (-(c / d)) ^ 2 = (c / d) ^ 2 := by ring
      rw [e2] at h1
      exact h1
    · exact one_sub_arctan_div_le h
  have e3 : (c / d) ^ 2 / 3 = c ^ 2 / (3 * d ^ 2) := by
    rw [div_pow, div_div]
    ring
  linarith [hk, e3]

/-- `Σ_{m<N} 1/(m−j)² ≤ π²/6` (natural subtraction; the terms with `m ≤ j` vanish). -/
theorem sum_inv_sq_shift_le (N j : ℕ) :
    ∑ m ∈ Finset.range N, (1 : ℝ) / ((m - j : ℕ) : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have h1 : ∑ m ∈ Finset.range N, (1 : ℝ) / ((m - j : ℕ) : ℝ) ^ 2 =
      ∑ m ∈ (Finset.range N).filter (fun k => j < k), (1 : ℝ) / ((m - j : ℕ) : ℝ) ^ 2 := by
    apply (Finset.sum_filter_of_ne _).symm
    intro m _ hm
    by_contra hjm
    apply hm
    have h0 : m - j = 0 := by omega
    simp [h0]
  have hinj : ∀ x ∈ (Finset.range N).filter (fun k => j < k),
      ∀ y ∈ (Finset.range N).filter (fun k => j < k), x - j = y - j → x = y := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    omega
  have h2 : ∑ m ∈ (Finset.range N).filter (fun k => j < k), (1 : ℝ) / ((m - j : ℕ) : ℝ) ^ 2 =
      ∑ x ∈ ((Finset.range N).filter (fun k => j < k)).image (fun k => k - j),
        (1 : ℝ) / (x : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
  have hsub : ((Finset.range N).filter (fun k => j < k)).image (fun k => k - j) ⊆
      Finset.range N := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, hkx⟩
    have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    rw [← hkx]
    exact Finset.mem_range.mpr (by omega)
  have h3 : ∑ x ∈ ((Finset.range N).filter (fun k => j < k)).image (fun k => k - j),
        (1 : ℝ) / (x : ℝ) ^ 2 ≤ ∑ x ∈ Finset.range N, (1 : ℝ) / (x : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have h4 : ∑ x ∈ Finset.range N, (1 : ℝ) / (x : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum (Finset.range N) (fun i _ => by positivity) hasSum_zeta_two
  rw [h1, h2]
  linarith

/-- Symmetric double sum of the defect: `Σ_{j,k} δ_c(q_j−q_k) = N + 2𝒟_N(q)` (diagonal value `δ_c(0) = 1`). -/
theorem sum_defect_eq {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    ∑ j : Fin N, ∑ k : Fin N, defect c (q j - q k) = (N : ℝ) + 2 * pairDefect c q := by
  have pt : ∀ j k : Fin N, defect c (q j - q k) =
      (if j = k then 1 else 0) + ((if j < k then defect c (q j - q k) else 0) +
        (if k < j then defect c (q j - q k) else 0)) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · have hne : j ≠ k := ne_of_lt h
      simp [h, hne, not_lt.2 h.le]
    · subst h
      simp [defect]
    · have hne : j ≠ k := ne_of_gt h
      simp [h, hne, not_lt.2 h.le]
  have hswap : ∑ j : Fin N, ∑ k : Fin N, (if k < j then defect c (q j - q k) else 0) =
      ∑ j : Fin N, ∑ k : Fin N, (if j < k then defect c (q j - q k) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    rw [show q x - q y = -(q y - q x) by ring, defect_neg]
  have hdiag : ∑ j : Fin N, ∑ k : Fin N, (if j = k then (1 : ℝ) else 0) = (N : ℝ) := by
    simp
  calc ∑ j : Fin N, ∑ k : Fin N, defect c (q j - q k)
      = ∑ j : Fin N, ∑ k : Fin N, ((if j = k then (1 : ℝ) else 0) +
          ((if j < k then defect c (q j - q k) else 0) +
            (if k < j then defect c (q j - q k) else 0))) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => pt j k))
    _ = (N : ℝ) + 2 * pairDefect c q := by
        simp only [Finset.sum_add_distrib]
        rw [hswap, hdiag]
        unfold pairDefect
        ring

/-! ## 4. The core estimate: adjacent spacing (source lines 43--73) -/

/-- Telescoping of the arctan differences. -/
theorem telescope_arctan (c d : ℝ) (p : ℕ) :
    ∑ m ∈ Finset.range p, (Real.arctan (((m : ℝ) + 1) * d / c) - Real.arctan ((m : ℝ) * d / c))
      = Real.arctan ((p : ℝ) * d / c) := by
  have h := Finset.sum_range_sub (fun m : ℕ => Real.arctan ((m : ℝ) * d / c)) p
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, zero_div, Real.arctan_zero,
    sub_zero] at h
  exact h

/-- `h_{c,d}(x) = arctan((x+d)/c) − arctan(x/c)` (source line 54). -/
def shiftH (c d x : ℝ) : ℝ := Real.arctan ((x + d) / c) - Real.arctan (x / c)

theorem shiftH_reflect (c d z : ℝ) : shiftH c d (-(z + d)) = shiftH c d z := by
  unfold shiftH
  have e1 : (-(z + d) + d) / c = -(z / c) := by ring
  have e2 : -(z + d) / c = -((z + d) / c) := by ring
  rw [e1, e2, Real.arctan_neg, Real.arctan_neg]
  ring

/-- `h_{c,d}` is decreasing on `[0, ∞)` (source line 54: `h` decreases for `x ≥ 0`). -/
theorem shiftH_antitone {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    AntitoneOn (shiftH c d) (Set.Ici 0) := by
  apply antitoneOn_Ici_of_hasDeriv
    (f' := fun t : ℝ => 1 / (1 + ((t + d) / c) ^ 2) * (1 / c) - 1 / (1 + (t / c) ^ 2) * (1 / c))
  · intro t _
    have h1 : HasDerivAt (fun x : ℝ => (x + d) / c) (1 / c) t :=
      ((hasDerivAt_id' t).add_const d).div_const c
    have h2 : HasDerivAt (fun x : ℝ => x / c) (1 / c) t := (hasDerivAt_id' t).div_const c
    exact (h1.arctan).sub (h2.arctan)
  · intro t ht
    have ht0 : 0 ≤ t := ht.le
    have hdiff : (t + d) / c - t / c = d / c := by ring
    have hdc : 0 ≤ d / c := div_nonneg hd hc.le
    have h0 : 0 ≤ t / c := div_nonneg ht0 hc.le
    have hab : t / c ≤ (t + d) / c := by linarith
    have hsq : (t / c) ^ 2 ≤ ((t + d) / c) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg h0 (le_trans h0 hab))]
    have hA : 1 / (1 + ((t + d) / c) ^ 2) ≤ 1 / (1 + (t / c) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hc1 : 0 ≤ 1 / c := by positivity
    have := mul_le_mul_of_nonneg_right hA hc1
    linarith

/-- Chain bound (source line 55--58): adjacent spacings `≥ d` give `m d ≤ Q(a+m) − Q a`. -/
theorem chain_bound {N : ℕ} (Q : ℕ → ℝ) (d : ℝ)
    (hmin : ∀ t, t + 1 < N → d ≤ Q (t + 1) - Q t) :
    ∀ m a : ℕ, a + m < N → (m : ℝ) * d ≤ Q (a + m) - Q a := by
  intro m
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    have h1 := ih a (by omega)
    have h2 := hmin (a + m) (by omega)
    have e : a + (m + 1) = a + m + 1 := by omega
    have e2 : ((m + 1 : ℕ) : ℝ) * d = (m : ℝ) * d + d := by push_cast; ring
    rw [e, e2]
    linarith

theorem aStar_pos {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L) : 0 < aStar κ L := by
  unfold aStar
  have hpos : 0 < 8 * κ / L := div_pos (by linarith) hL
  have hs2 : Real.sqrt (κ ^ 2 + 8 * κ / L) ^ 2 = κ ^ 2 + 8 * κ / L :=
    Real.sq_sqrt (by linarith [sq_nonneg κ])
  have hs0 := Real.sqrt_nonneg (κ ^ 2 + 8 * κ / L)
  nlinarith

/-- The defining identity of `a_*`: `L a_*(a_* + 2κ) = 8κ`. -/
theorem aStar_identity {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L) :
    L * (aStar κ L * (aStar κ L + 2 * κ)) = 8 * κ := by
  unfold aStar
  have hpos : 0 < 8 * κ / L := div_pos (by linarith) hL
  have hs2 : Real.sqrt (κ ^ 2 + 8 * κ / L) ^ 2 = κ ^ 2 + 8 * κ / L :=
    Real.sq_sqrt (by linarith [sq_nonneg κ])
  have e : L * ((Real.sqrt (κ ^ 2 + 8 * κ / L) - κ) *
      (Real.sqrt (κ ^ 2 + 8 * κ / L) - κ + 2 * κ)) =
      L * (Real.sqrt (κ ^ 2 + 8 * κ / L) ^ 2 - κ ^ 2) := by ring
  rw [e, hs2]
  field_simp
  try ring

set_option maxHeartbeats 1000000 in
/-- **Core estimate.** For an ℕ-indexed on-shell chain with `c = κ/N`, the adjacent spacing at `i`
is at least `a_*/N`, given that it is the minimal adjacent spacing (source lines 44--73). -/
theorem core_spacing {N : ℕ} {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 1 ≤ N)
    (Q I : ℕ → ℝ)
    (hE : ∀ j, j < N → L * Q j + 2 * ∑ k ∈ Finset.range N,
        Real.arctan ((Q j - Q k) / (κ / (N : ℝ))) = 2 * Real.pi * I j)
    (hI : ∀ t, t + 1 < N → I t + 1 ≤ I (t + 1))
    (i : ℕ) (hi : i + 1 < N) (hpos : 0 < Q (i + 1) - Q i)
    (hmin : ∀ t, t + 1 < N → Q (i + 1) - Q i ≤ Q (t + 1) - Q t) :
    aStar κ L / (N : ℝ) ≤ Q (i + 1) - Q i := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = κ / (N : ℝ) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact div_pos hκ hNpos
  rw [← hcdef] at hE
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = Q (i + 1) - Q i := ⟨_, rfl⟩
  rw [← hddef] at hpos hmin ⊢
  have hd0 : 0 ≤ d := hpos.le
  have hQ1 : Q (i + 1) = Q i + d := by linarith
  -- Step 1 (source lines 44--52): difference of the rapidity equations at i+1 and i.
  have E1 := hE i (by omega)
  have E2 := hE (i + 1) hi
  rw [hQ1] at E2
  have hI' := hI i hi
  have hpi : 2 * Real.pi * (I i + 1) ≤ 2 * Real.pi * I (i + 1) :=
    mul_le_mul_of_nonneg_left hI' (by positivity)
  have hS : ∑ k ∈ Finset.range N, Real.arctan ((Q i + d - Q k) / c)
      - ∑ k ∈ Finset.range N, Real.arctan ((Q i - Q k) / c)
      = ∑ k ∈ Finset.range N, shiftH c d (Q i - Q k) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold shiftH
    rw [show Q i + d - Q k = (Q i - Q k) + d by ring]
  have hkey : L * d + 2 * ∑ k ∈ Finset.range N, shiftH c d (Q i - Q k) ≥ 2 * Real.pi := by
    rw [← hS]
    linarith
  -- Steps 2--3 (source lines 55--63): termwise comparison with equally spaced sums.
  have hchain := chain_bound Q d hmin
  have hterm : ∀ k ∈ Finset.range N, shiftH c d (Q i - Q k) ≤
      (if k ≤ i then shiftH c d (((i - k : ℕ) : ℝ) * d)
        else shiftH c d (((k - (i + 1) : ℕ) : ℝ) * d)) := by
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    by_cases hki : k ≤ i
    · rw [if_pos hki]
      have hx := hchain (i - k) k (by omega)
      rw [show k + (i - k) = i by omega] at hx
      have hy : 0 ≤ ((i - k : ℕ) : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd0
      exact shiftH_antitone hc hd0 (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr (le_trans hy hx)) hx
    · rw [if_neg hki]
      push_neg at hki
      have hx := hchain (k - (i + 1)) (i + 1) (by omega)
      rw [show i + 1 + (k - (i + 1)) = k by omega, hQ1] at hx
      have hrefl : Q i - Q k = -((Q k - Q i - d) + d) := by ring
      rw [hrefl, shiftH_reflect]
      have hy : 0 ≤ ((k - (i + 1) : ℕ) : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd0
      have hx' : ((k - (i + 1) : ℕ) : ℝ) * d ≤ Q k - Q i - d := by linarith
      exact shiftH_antitone hc hd0 (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr (le_trans hy hx')) hx'
  -- Step 4: splitting the comparison sum at `i`.
  have hsplit : ∑ k ∈ Finset.range N, (if k ≤ i then shiftH c d (((i - k : ℕ) : ℝ) * d)
        else shiftH c d (((k - (i + 1) : ℕ) : ℝ) * d))
      = ∑ m ∈ Finset.range (i + 1), shiftH c d ((m : ℝ) * d)
        + ∑ m ∈ Finset.range (N - (i + 1)), shiftH c d ((m : ℝ) * d) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ N by omega)]
    congr 1
    · refine Eq.trans (Finset.sum_congr rfl ?_)
        (Finset.sum_range_reflect (fun m : ℕ => shiftH c d ((m : ℝ) * d)) (i + 1))
      intro k hk
      have hk' : k < i + 1 := Finset.mem_range.mp hk
      simp only [Nat.add_sub_cancel, if_pos (show k ≤ i by omega)]
    · rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show (if i + 1 + k ≤ i then shiftH c d (((i - (i + 1 + k) : ℕ) : ℝ) * d)
          else shiftH c d (((i + 1 + k - (i + 1) : ℕ) : ℝ) * d)) = shiftH c d ((k : ℝ) * d)
      rw [if_neg (show ¬ (i + 1 + k ≤ i) by omega), show i + 1 + k - (i + 1) = k by omega]
  -- Step 5: telescoping (source line 54--58, equally spaced sums).
  have htel1 : ∑ m ∈ Finset.range (i + 1), shiftH c d ((m : ℝ) * d) =
      Real.arctan (((i + 1 : ℕ) : ℝ) * d / c) := by
    rw [← telescope_arctan c d (i + 1)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold shiftH
    rw [show (m : ℝ) * d + d = ((m : ℝ) + 1) * d by ring]
  have htel2 : ∑ m ∈ Finset.range (N - (i + 1)), shiftH c d ((m : ℝ) * d) =
      Real.arctan (((N - (i + 1) : ℕ) : ℝ) * d / c) := by
    rw [← telescope_arctan c d (N - (i + 1))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold shiftH
    rw [show (m : ℝ) * d + d = ((m : ℝ) + 1) * d by ring]
  have hA0 : 0 ≤ ((i + 1 : ℕ) : ℝ) * d / c :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd0) hc.le
  have hB0 : 0 ≤ ((N - (i + 1) : ℕ) : ℝ) * d / c :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd0) hc.le
  have hSbound : ∑ k ∈ Finset.range N, shiftH c d (Q i - Q k) ≤
      Real.arctan (((i + 1 : ℕ) : ℝ) * d / c) + Real.arctan (((N - (i + 1) : ℕ) : ℝ) * d / c) := by
    rw [← htel1, ← htel2, ← hsplit]
    exact Finset.sum_le_sum hterm
  -- Step 6--7: concavity of arctan on `[0,∞)` (the pair of equally spaced sums).
  have hsum_cast : ((i + 1 : ℕ) : ℝ) + ((N - (i + 1) : ℕ) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub (show i + 1 ≤ N by omega)]
    ring
  have hx : (((i + 1 : ℕ) : ℝ) * d / c + ((N - (i + 1) : ℕ) : ℝ) * d / c) / 2
      = (N : ℝ) * d / (2 * c) := by
    rw [← hsum_cast]
    field_simp
    try ring
  have hconc := arctan_add_le hA0 hB0
  rw [hx] at hconc
  have hS_le : ∑ k ∈ Finset.range N, shiftH c d (Q i - Q k) ≤
      2 * Real.arctan ((N : ℝ) * d / (2 * c)) := by linarith
  have hkey2 : L * d + 4 * Real.arctan ((N : ℝ) * d / (2 * c)) ≥ 2 * Real.pi := by linarith
  -- Step 8 (source line 66): inverse arctan identity, x⁻¹ = (1/N)(2κ/(Nd)).
  have hxpos : 0 < (N : ℝ) * d / (2 * c) := div_pos (mul_pos hNpos hpos) (by linarith)
  have hinv := Real.arctan_inv_of_pos hxpos
  have hxinv : ((N : ℝ) * d / (2 * c))⁻¹ = (1 / (N : ℝ)) * (2 * κ / ((N : ℝ) * d)) := by
    rw [hcdef]
    field_simp
    try ring
  rw [hxinv] at hinv
  have hLd : 4 * ((1 / (N : ℝ)) * Real.arctan (2 * κ / ((N : ℝ) * d))) ≤ L * d := by
    have hsc := arctan_scale_le (s := 1 / (N : ℝ)) (y := 2 * κ / ((N : ℝ) * d))
      (by positivity) (by rw [div_le_one hNpos]; exact_mod_cast hN)
      (div_nonneg (by linarith) (mul_nonneg hNpos.le hd0))
    linarith
  have hLa : 4 * Real.arctan (2 * κ / ((N : ℝ) * d)) ≤ L * ((N : ℝ) * d) := by
    have e6 : (N : ℝ) * (4 * ((1 / (N : ℝ)) * Real.arctan (2 * κ / ((N : ℝ) * d)))) =
        4 * Real.arctan (2 * κ / ((N : ℝ) * d)) := by
      field_simp
      try ring
    calc 4 * Real.arctan (2 * κ / ((N : ℝ) * d))
        = (N : ℝ) * (4 * ((1 / (N : ℝ)) * Real.arctan (2 * κ / ((N : ℝ) * d)))) := e6.symm
      _ ≤ (N : ℝ) * (L * d) := mul_le_mul_of_nonneg_left hLd hNpos.le
      _ = L * ((N : ℝ) * d) := by ring
  -- Step 9 (source lines 66--71): arctan y ≥ y/(1+y) for y = 2κ/a, a = Nd.
  have hya : 0 ≤ 2 * κ / ((N : ℝ) * d) := div_nonneg (by linarith) (mul_nonneg hNpos.le hd0)
  have hdiv := div_one_add_le_arctan hya
  have hane : (N : ℝ) * d ≠ 0 := (mul_pos hNpos hpos).ne'
  have hane2 : (N : ℝ) * d + 2 * κ ≠ 0 := by
    have := mul_pos hNpos hpos
    exact (by linarith : (0 : ℝ) < (N : ℝ) * d + 2 * κ).ne'
  have hy1 : (2 * κ / ((N : ℝ) * d)) / (1 + 2 * κ / ((N : ℝ) * d)) =
      2 * κ / ((N : ℝ) * d + 2 * κ) := by
    field_simp
    try ring
  have h8 : 8 * κ / ((N : ℝ) * d + 2 * κ) ≤ L * ((N : ℝ) * d) := by
    have e8 : 8 * κ / ((N : ℝ) * d + 2 * κ) =
        4 * ((2 * κ / ((N : ℝ) * d)) / (1 + 2 * κ / ((N : ℝ) * d))) := by
      rw [hy1]
      ring
    rw [e8]
    linarith
  have hpos2 : 0 < (N : ℝ) * d + 2 * κ := by
    have := mul_pos hNpos hpos
    linarith
  rw [div_le_iff₀ hpos2] at h8
  -- Step 10 (source lines 71--73): the quadratic inequality gives a ≥ a_*.
  have hid := aStar_identity hκ hL
  have has := aStar_pos hκ hL
  have hprod : 0 ≤ L * (((N : ℝ) * d - aStar κ L) * ((N : ℝ) * d + aStar κ L + 2 * κ)) := by
    linarith [h8, hid]
  have hX : 0 ≤ ((N : ℝ) * d - aStar κ L) * ((N : ℝ) * d + aStar κ L + 2 * κ) :=
    (mul_nonneg_iff_of_pos_left hL).1 hprod
  have hP : 0 < (N : ℝ) * d + aStar κ L + 2 * κ := by
    have := mul_pos hNpos hpos
    linarith
  have hge : 0 ≤ (N : ℝ) * d - aStar κ L :=
    (mul_nonneg_iff_of_pos_right hP).1 hX
  rw [div_le_iff₀ hNpos]
  linarith

/-! ## 5. Convention bridge: printed on-shell ⟹ DEF-006 rapidity equation ⟹ accepted roots -/

/-- Fin-indexed DEF-006 rapidity equation, transported to the ℕ-indexed `range` form. -/
theorem rapidity_range {N : ℕ} {L c : ℝ} (q : Fin N → ℝ) (I : Fin N → ℝ) (j : Fin N)
    (hE : L * q j + 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c)
      = 2 * Real.pi * I j) :
    L * Qd q (j : ℕ) + 2 * ∑ k ∈ Finset.range N, Real.arctan ((Qd q (j : ℕ) - Qd q k) / c)
      = 2 * Real.pi * I j := by
  have h1 : ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c)
      = ∑ k : Fin N, Real.arctan ((q j - q k) / c) :=
    Finset.sum_erase _ (by simp)
  have h2 : ∑ k : Fin N, Real.arctan ((q j - q k) / c)
      = ∑ m ∈ Finset.range N, Real.arctan ((q j - Qd q m) / c) :=
    sum_fin_eq_range q (fun x => Real.arctan ((q j - x) / c))
  rw [Qd_val]
  rw [h1, h2] at hE
  exact hE

/-- Printed Bethe form ⟹ DEF-006 rapidity equation with labels `quantumNumbers n` (`RapidityEq`).
Uses the arctan inversion `2arctan((x)/c) + 2arctan(c/x) = π sgn x` and the sign count. -/
theorem rapidity_of_printed {M : ℕ} {L c : ℝ} (hc : 0 < c) (n : Fin (M + 1) → ℤ)
    (q : Fin (M + 1) → ℝ) (hq : StrictMono q)
    (hP : ∀ i : Fin (M + 1), L * q i = 2 * Real.pi * (n i : ℝ) +
      2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (c / (q i - q k))) :
    RapidityEq L c (quantumNumbers n) q := by
  unfold RapidityEq
  intro j
  have hpair : ∀ k ∈ Finset.univ.erase j,
      2 * Real.arctan ((q j - q k) / c) + 2 * Real.arctan (c / (q j - q k)) =
        if k < j then Real.pi else -Real.pi := by
    intro k hk
    have hne : k ≠ j := Finset.ne_of_mem_erase hk
    have hx : q j - q k ≠ 0 := by
      intro e
      exact hne (hq.injective (sub_eq_zero.1 e)).symm
    rw [pair_identity hc hx]
    simp only [sub_pos, hq.lt_iff_lt]
  have hsplit : ∑ k ∈ Finset.univ.erase j,
      (2 * Real.arctan ((q j - q k) / c) + 2 * Real.arctan (c / (q j - q k))) =
        ∑ k ∈ Finset.univ.erase j, (if k < j then Real.pi else -Real.pi) :=
    Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, count_erase] at hsplit
  have hP' := hP j
  unfold quantumNumbers
  push_cast
  linarith

/-- Successor increment of the DEF-006 labels: `I_{t+1} − I_t = n_{t+1} − n_t + 1 ≥ 1`. -/
theorem Idd_step {N : ℕ} {n : Fin N → ℤ} (hn : Monotone n) (t : ℕ) (ht : t + 1 < N) :
    Idd n t + 1 ≤ Idd n (t + 1) := by
  have h1 : t < N := by omega
  unfold Idd
  rw [dif_pos h1, dif_pos ht]
  have hle : n ⟨t, h1⟩ ≤ n ⟨t + 1, ht⟩ := hn (Fin.mk_le_mk.2 (Nat.le_succ t))
  have hle' : (n ⟨t, h1⟩ : ℝ) ≤ (n ⟨t + 1, ht⟩ : ℝ) := by exact_mod_cast hle
  unfold quantumNumbers
  push_cast
  linarith

/-- **Convention bridge (R-4C8D7C9E / DEF-006).** For `N ≥ 1`, `OrderedOnShell L κ n q` holds exactly when
`q` is the accepted root vector `BetheSmooth.roots L n (κ/N)` of the corrected integers `n`. -/
theorem ordered_onshell_iff_roots {N : ℕ} (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (n : Fin N → ℤ) (hn : Monotone n) (q : Fin N → ℝ) :
    OrderedOnShell L κ n q ↔ q = QuantumNLS.BetheSmooth.roots L n (κ / (N : ℝ)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hc : 0 < κ / ((M + 1 : ℕ) : ℝ) := div_pos hκ (by positivity)
  have hcorr : correctedInt (labelsOf ⟨n, hn⟩) = n := by
    funext j
    have h := correctedInt_spec (labelsOf ⟨n, hn⟩) j
    have h2 := corrected_recovery n j
    have h3 : ((correctedInt (labelsOf ⟨n, hn⟩) j : ℤ) : ℝ) = (n j : ℝ) := by
      rw [h]
      simpa [labelsOf] using h2
    exact_mod_cast h3
  unfold OrderedOnShell
  constructor
  · rintro ⟨hmono, _, hP⟩
    have hPc : ∀ i : Fin (M + 1), L * q i = 2 * Real.pi * (n i : ℝ) +
        2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (κ / ((M + 1 : ℕ) : ℝ) / (q i - q k)) := by
      intro i
      rw [hP i]
      simp only [div_div]
    have hE := rapidity_of_printed hc n q hmono hPc
    have hroots := (rapidityEq_iff_roots hL hc (labelsOf ⟨n, hn⟩) q).1 hE
    rw [hcorr] at hroots
    exact hroots
  · intro hq
    subst hq
    have hR : QuantumNLS.BetheSmooth.roots L n (κ / ((M + 1 : ℕ) : ℝ)) =
        QuantumNLS.BetheSmooth.roots L (correctedInt (labelsOf ⟨n, hn⟩))
          (κ / ((M + 1 : ℕ) : ℝ)) := by
      rw [hcorr]
    have hE : RapidityEq L (κ / ((M + 1 : ℕ) : ℝ)) (labelsOf ⟨n, hn⟩).I
        (QuantumNLS.BetheSmooth.roots L n (κ / ((M + 1 : ℕ) : ℝ))) := by
      rw [hR]
      exact (rapidityEq_iff_roots hL hc (labelsOf ⟨n, hn⟩) _).2 rfl
    have hmono : StrictMono (QuantumNLS.BetheSmooth.roots L n (κ / ((M + 1 : ℕ) : ℝ))) := by
      have h := roots_strictMono_labels hL hc (labelsOf ⟨n, hn⟩)
      rw [hcorr] at h
      exact h
    refine ⟨hmono, hn, fun j => ?_⟩
    have hb := bethe_printed hc (labelsOf ⟨n, hn⟩) _ L hmono hE j
    rw [hcorr] at hb
    simp only [← div_div]
    linarith

/-! ## 6. The empirical measure and the double integral -/

/-- Integral of a function against `L_N = N⁻¹ Σ_j δ_{q_j}`. -/
theorem integral_empMeasure (N : ℕ) (q : Fin N → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(empMeasure N q) = (N : ℝ)⁻¹ * ∑ j : Fin N, f (q j) := by
  unfold empMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro j _
    exact integrable_dirac (by simp)

/-- The iterated integral `∬ δ_c(t−u) dL_N(t) dL_N(u)` as a finite double sum. -/
theorem double_integral_empMeasure (N : ℕ) (c : ℝ) (q : Fin N → ℝ) :
    ∫ t, ∫ u, defect c (t - u) ∂(empMeasure N q) ∂(empMeasure N q) =
      (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ j : Fin N, ∑ k : Fin N, defect c (q j - q k)) := by
  have inner : ∀ t : ℝ, ∫ u, defect c (t - u) ∂(empMeasure N q) =
      (N : ℝ)⁻¹ * ∑ k : Fin N, defect c (t - q k) :=
    fun t => integral_empMeasure N q (fun u => defect c (t - u))
  simp only [inner]
  rw [integral_empMeasure N q (fun t => (N : ℝ)⁻¹ * ∑ k : Fin N, defect c (t - q k))]
  congr 1
  rw [← Finset.mul_sum]

set_option maxHeartbeats 1000000 in
/-- **Pair-defect bound (source lines 75--85).** For an ordered configuration with the spacing bound,
`𝒟_N(q) ≤ N C_pair`. -/
theorem pairDefect_le {N : ℕ} {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 1 ≤ N)
    (q : Fin N → ℝ) (hmono : StrictMono q)
    (hstep : ∀ t, t + 1 < N → aStar κ L / (N : ℝ) ≤ Qd q (t + 1) - Qd q t) :
    pairDefect (κ / (N : ℝ)) q ≤ (N : ℝ) * Cpair κ L := by
  have ha : 0 < aStar κ L := aStar_pos hκ hL
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hterm : ∀ j k : Fin N,
      (if j < k then defect (κ / (N : ℝ)) (q j - q k) else 0) ≤
        (if j < k then κ ^ 2 / (3 * aStar κ L ^ 2) * (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2)
          else 0) := by
    intro j k
    by_cases hjk : j < k
    · rw [if_pos hjk, if_pos hjk]
      have hjk' : (j : ℕ) < (k : ℕ) := hjk
      have hkN : (k : ℕ) < N := k.isLt
      have hne : q j - q k ≠ 0 := sub_ne_zero.2 (hmono hjk).ne
      have hdef := defect_le (c := κ / (N : ℝ)) (d := q j - q k) (div_pos hκ hNpos) hne
      have hchain := chain_bound (Qd q) (aStar κ L / (N : ℝ)) hstep ((k : ℕ) - (j : ℕ)) (j : ℕ)
        (by omega)
      rw [show (j : ℕ) + ((k : ℕ) - (j : ℕ)) = (k : ℕ) by omega, Qd_val, Qd_val] at hchain
      have hm1 : (1 : ℝ) ≤ (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) := by
        have : 1 ≤ (k : ℕ) - (j : ℕ) := by omega
        exact_mod_cast this
      have hm0 : (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ≠ 0 := ne_of_gt (by linarith)
      have hmpos : 0 < (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) * (aStar κ L / (N : ℝ)) :=
        mul_pos (by linarith) (div_pos ha hNpos)
      have hsq : ((((k : ℕ) - (j : ℕ) : ℕ) : ℝ) * (aStar κ L / (N : ℝ))) ^ 2 ≤
          (q j - q k) ^ 2 := by
        have h := mul_le_mul hchain hchain hmpos.le (by linarith)
        nlinarith [h]
      have hFpos : 0 < ((((k : ℕ) - (j : ℕ) : ℕ) : ℝ) * (aStar κ L / (N : ℝ))) ^ 2 :=
        pow_pos hmpos 2
      have hinv := one_div_le_one_div_of_le hFpos hsq
      have hane : aStar κ L ≠ 0 := ha.ne'
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      have e1 : (κ / (N : ℝ)) ^ 2 / (3 * (q j - q k) ^ 2)
          = ((κ / (N : ℝ)) ^ 2 / 3) * (1 / (q j - q k) ^ 2) := by
        rw [mul_one_div, div_div]
      have e2 : ((κ / (N : ℝ)) ^ 2 / 3) *
          (1 / ((((k : ℕ) - (j : ℕ) : ℕ) : ℝ) * (aStar κ L / (N : ℝ))) ^ 2)
          = κ ^ 2 / (3 * aStar κ L ^ 2) * (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2) := by
        field_simp
        try ring
      calc defect (κ / (N : ℝ)) (q j - q k)
          ≤ (κ / (N : ℝ)) ^ 2 / (3 * (q j - q k) ^ 2) := hdef
        _ = ((κ / (N : ℝ)) ^ 2 / 3) * (1 / (q j - q k) ^ 2) := e1
        _ ≤ ((κ / (N : ℝ)) ^ 2 / 3) *
            (1 / ((((k : ℕ) - (j : ℕ) : ℕ) : ℝ) * (aStar κ L / (N : ℝ))) ^ 2) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = κ ^ 2 / (3 * aStar κ L ^ 2) * (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2) := e2
    · simp [hjk]
  calc pairDefect (κ / (N : ℝ)) q
      ≤ ∑ j : Fin N, ∑ k : Fin N, (if j < k then
          κ ^ 2 / (3 * aStar κ L ^ 2) * (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2) else 0) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hterm j k))
    _ = ∑ j : Fin N, κ ^ 2 / (3 * aStar κ L ^ 2) *
          ∑ m ∈ Finset.range N, (1 : ℝ) / (((m - (j : ℕ) : ℕ) : ℝ)) ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hk : ∀ k : Fin N, (if j < k then κ ^ 2 / (3 * aStar κ L ^ 2) *
            (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2) else 0) =
            κ ^ 2 / (3 * aStar κ L ^ 2) * (1 / (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) ^ 2) := by
          intro k
          by_cases hjk : j < k
          · rw [if_pos hjk]
          · have h0 : (k : ℕ) - (j : ℕ) = 0 := by
              have : (k : ℕ) ≤ (j : ℕ) := Fin.le_iff_val_le_val.1 (not_lt.1 hjk)
              omega
            rw [if_neg hjk, h0]
            simp
        rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun m => (1 : ℝ) / (((m - (j : ℕ) : ℕ) : ℝ)) ^ 2) N
    _ ≤ ∑ j : Fin N, κ ^ 2 / (3 * aStar κ L ^ 2) * (Real.pi ^ 2 / 6) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (sum_inv_sq_shift_le N (j : ℕ)) (by positivity))
    _ = (N : ℝ) * Cpair κ L := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold Cpair
        ring

/-! ## 7. The main statement -/

/-- **R-2EF16A1A (`lem:EP-spacing`).** For `N ≥ 1` and every ordered on-shell configuration:
for `N ≥ 2` the adjacent spacing is at least `a_*/N`; `𝒟_N(q) ≤ N C_pair` and
`∬ δ_c(t−u) dL_N(t) dL_N(u) ≤ C_δ/N` with `c = κ/N` (the last two for every `N ≥ 1`). -/
theorem lem_EP_spacing {N : ℕ} (hN : 1 ≤ N) {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ)
    (n : Fin N → ℤ) (q : Fin N → ℝ) (h : OrderedOnShell L κ n q) :
    (2 ≤ N → ∀ i j : Fin N, j.val = i.val + 1 → aStar κ L / (N : ℝ) ≤ q j - q i) ∧
    pairDefect (κ / (N : ℝ)) q ≤ (N : ℝ) * Cpair κ L ∧
    ∫ t, ∫ u, defect (κ / (N : ℝ)) (t - u) ∂(empMeasure N q) ∂(empMeasure N q)
      ≤ Cdelta κ L / (N : ℝ) := by
  unfold OrderedOnShell at h
  obtain ⟨hmono, hnmono, hP⟩ := h
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hNpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < M + 1 by omega)
  have hNne : ((M + 1 : ℕ) : ℝ) ≠ 0 := hNpos.ne'
  have hc : 0 < κ / ((M + 1 : ℕ) : ℝ) := div_pos hκ hNpos
  have hPc : ∀ i : Fin (M + 1), L * q i = 2 * Real.pi * (n i : ℝ) +
      2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (κ / ((M + 1 : ℕ) : ℝ) / (q i - q k)) := by
    intro i
    rw [hP i]
    simp only [div_div]
  have hE := rapidity_of_printed hc n q hmono hPc
  have hEc : ∀ j, j < M + 1 → L * Qd q j + 2 * ∑ k ∈ Finset.range (M + 1),
      Real.arctan ((Qd q j - Qd q k) / (κ / ((M + 1 : ℕ) : ℝ))) =
        2 * Real.pi * Idd n j := by
    intro j hj
    have := rapidity_range q (quantumNumbers n) ⟨j, hj⟩ (hE ⟨j, hj⟩)
    unfold Idd
    rw [dif_pos hj]
    exact this
  have hI : ∀ t, t + 1 < M + 1 → Idd n t + 1 ≤ Idd n (t + 1) :=
    fun t ht => Idd_step hnmono t ht
  -- Minimal adjacent spacing and the bound `a_*/N` for every adjacent pair (source line 44--73).
  have hstep : ∀ t, t + 1 < M + 1 →
      aStar κ L / ((M + 1 : ℕ) : ℝ) ≤ Qd q (t + 1) - Qd q t := by
    intro t ht
    obtain ⟨t0, ht0, hmin0⟩ := Finset.exists_min_image (Finset.range M)
      (fun s => Qd q (s + 1) - Qd q s) ⟨t, Finset.mem_range.mpr (by omega)⟩
    have ht0' : t0 + 1 < M + 1 := by
      have := Finset.mem_range.mp ht0
      omega
    have hmin' : ∀ s, s + 1 < M + 1 → Qd q (t0 + 1) - Qd q t0 ≤ Qd q (s + 1) - Qd q s := by
      intro s hs
      exact hmin0 s (Finset.mem_range.mpr (by omega))
    have hcore := core_spacing (N := M + 1) hL hκ (by omega) (Qd q) (Idd n) hEc hI t0 ht0'
      (by linarith [Qd_lt hmono ht0']) hmin'
    exact le_trans hcore (hmin' t ht)
  have part1 : 2 ≤ M + 1 → ∀ i j : Fin (M + 1), j.val = i.val + 1 →
      aStar κ L / ((M + 1 : ℕ) : ℝ) ≤ q j - q i := by
    intro _ i j hij
    have hi1 : i.val + 1 < M + 1 := by
      have := j.isLt
      omega
    have h1 := hstep i.val hi1
    have h2 : Qd q (i.val + 1) = q j := by
      rw [show i.val + 1 = j.val from hij.symm]
      exact Qd_val q j
    have h3 : Qd q i.val = q i := Qd_val q i
    rw [h2, h3] at h1
    exact h1
  have part2 := pairDefect_le hL hκ (by omega) q hmono hstep
  have part3 : ∫ t, ∫ u, defect (κ / ((M + 1 : ℕ) : ℝ)) (t - u) ∂(empMeasure (M + 1) q)
      ∂(empMeasure (M + 1) q) ≤ Cdelta κ L / ((M + 1 : ℕ) : ℝ) := by
    rw [double_integral_empMeasure, sum_defect_eq]
    have hinv : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have h4 : ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ)⁻¹ *
        (((M + 1 : ℕ) : ℝ) + 2 * pairDefect (κ / ((M + 1 : ℕ) : ℝ)) q)) ≤
        ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ)⁻¹ *
        (((M + 1 : ℕ) : ℝ) + 2 * (((M + 1 : ℕ) : ℝ) * Cpair κ L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hinv) hinv
    have h5 : ((M + 1 : ℕ) : ℝ)⁻¹ * (((M + 1 : ℕ) : ℝ)⁻¹ *
        (((M + 1 : ℕ) : ℝ) + 2 * (((M + 1 : ℕ) : ℝ) * Cpair κ L))) =
        Cdelta κ L / ((M + 1 : ℕ) : ℝ) := by
      unfold Cdelta
      field_simp
      try ring
    exact le_trans h4 (le_of_eq h5)
  exact ⟨part1, part2, part3⟩

/-! ## 8. Axiom audit (every declaration in this module) -/
#print axioms QuantumNLS.OnShellSpacing.lem_EP_spacing
#print axioms QuantumNLS.OnShellSpacing.ordered_onshell_iff_roots
#print axioms QuantumNLS.OnShellSpacing.core_spacing
#print axioms QuantumNLS.OnShellSpacing.pairDefect_le
#print axioms QuantumNLS.OnShellSpacing.double_integral_empMeasure
#print axioms QuantumNLS.OnShellSpacing.integral_empMeasure
#print axioms QuantumNLS.OnShellSpacing.sum_defect_eq
#print axioms QuantumNLS.OnShellSpacing.rapidity_of_printed
#print axioms QuantumNLS.OnShellSpacing.rapidity_range
#print axioms QuantumNLS.OnShellSpacing.Idd_step
#print axioms QuantumNLS.OnShellSpacing.arctan_concaveOn
#print axioms QuantumNLS.OnShellSpacing.arctan_add_le
#print axioms QuantumNLS.OnShellSpacing.arctan_scale_le
#print axioms QuantumNLS.OnShellSpacing.div_one_add_le_arctan
#print axioms QuantumNLS.OnShellSpacing.arctan_ge_cubic
#print axioms QuantumNLS.OnShellSpacing.one_sub_arctan_div_le
#print axioms QuantumNLS.OnShellSpacing.defect_neg
#print axioms QuantumNLS.OnShellSpacing.defect_le
#print axioms QuantumNLS.OnShellSpacing.sum_inv_sq_shift_le
#print axioms QuantumNLS.OnShellSpacing.telescope_arctan
#print axioms QuantumNLS.OnShellSpacing.shiftH_reflect
#print axioms QuantumNLS.OnShellSpacing.shiftH_antitone
#print axioms QuantumNLS.OnShellSpacing.chain_bound
#print axioms QuantumNLS.OnShellSpacing.aStar_pos
#print axioms QuantumNLS.OnShellSpacing.aStar_identity
#print axioms QuantumNLS.OnShellSpacing.sum_fin_eq_range
#print axioms QuantumNLS.OnShellSpacing.Qd_lt

end QuantumNLS.OnShellSpacing
