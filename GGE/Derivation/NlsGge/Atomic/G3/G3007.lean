import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2048
import NlsGge.Atomic.G2.G2074
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G2.G2022

/- G3-007 BOUND SUPPORT01 (proof development, AUTHOR; not self-reviewed).
   Supporting module for STATEMENTS/G3.md "## G3-007" (STOP item 2, proof development/G3007_STOP.md).
   Proves, with no added hypothesis, a neighbourhood V of phi0 in sourceW, a constant C > 0 and
   ||psiZeta phi (p2Extend38 n (sourceF n phi)) n m z|| <= C * Lib.c3w n m
   for all phi in V, m != n and z in closedBall (discC phi0 m) (discR phi0 m).
   Inputs (landed): fixed_family_persistence38, g2019_root_sep_core, g2019_closed_ball_dist,
   g2019_standardRoot_pair, g2019_radius_bound (G2-019); G2_074 (uniform l2 mass of the roots);
   g2075_root_eq_sigma (G2-075); stdRoot_ratio_bound38 (branch-safe ratio); Lib.norm_tprod_one_add_le. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Ratio estimate with the branch-safe bound from `stdRoot_ratio_bound38`. -/
theorem g3007_ratio_error {τ g A z w : ℂ} (hw_def : w = stdRoot38 τ g z) (hu : τ - z ≠ 0)
    (hw : w ≠ 0) :
    ‖(τ + g * A - z) / w - 1‖ ≤ (‖g‖ / (4 * ‖τ - z‖) + ‖g‖ * ‖A‖) / ‖w‖ := by
  have hδ := stdRoot_ratio_bound38 (τ := τ) (g2 := g) (z := z) hu
  subst hw_def
  set δ : ℂ := stdRoot38 τ g z / (τ - z) - 1 with hδdef
  have key : (τ + g * A - z) / stdRoot38 τ g z - 1
      = (-((τ - z) * δ) + g * A) / stdRoot38 τ g z := by
    rw [hδdef]
    field_simp
    ring
  have hpos : 0 < ‖τ - z‖ := norm_pos_iff.mpr hu
  have h1 : ‖-((τ - z) * δ) + g * A‖ ≤ ‖τ - z‖ * ‖δ‖ + ‖g‖ * ‖A‖ := by
    calc ‖-((τ - z) * δ) + g * A‖ ≤ ‖-((τ - z) * δ)‖ + ‖g * A‖ := norm_add_le _ _
      _ = ‖τ - z‖ * ‖δ‖ + ‖g‖ * ‖A‖ := by rw [norm_neg, norm_mul, norm_mul]
  have h2 : ‖τ - z‖ * ‖δ‖ ≤ ‖g‖ / (4 * ‖τ - z‖) := by
    calc ‖τ - z‖ * ‖δ‖ ≤ ‖τ - z‖ * (‖g‖ / (4 * ‖τ - z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hδ hpos.le
      _ = ‖g‖ / (4 * ‖τ - z‖) := by field_simp
  rw [key, norm_div]
  gcongr
  linarith

/-- Real estimate: AM-GM on `‖A‖ / j` with the lower bounds `c⁻¹ j` for both norms. -/
theorem g3007_real_bound {x y p q j c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hj : 0 < j)
    (hx : c⁻¹ * j ≤ x) (hy : c⁻¹ * j ≤ y) (hp : 0 ≤ p) (hp4 : p ≤ 4 * M ^ 2) (hq : 0 ≤ q) :
    (p / (4 * x) + p * q) / y ≤ (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) / j ^ 2 + 2 * c * M ^ 2 * q ^ 2 := by
  have hcj : 0 < c⁻¹ * j := mul_pos (inv_pos.mpr hc) hj
  have hx0 : 0 < x := lt_of_lt_of_le hcj hx
  have hy0 : 0 < y := lt_of_lt_of_le hcj hy
  have hcne : c ≠ 0 := hc.ne'
  have hjne : j ≠ 0 := hj.ne'
  have hxne : x ≠ 0 := hx0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  have h1 : p / (4 * x) ≤ M ^ 2 * c / j := by
    calc p / (4 * x) ≤ (4 * M ^ 2) / (4 * x) := by gcongr
      _ = M ^ 2 / x := by field_simp
      _ ≤ M ^ 2 / (c⁻¹ * j) := by gcongr
      _ = M ^ 2 * c / j := by field_simp
  have h2 : 1 / y ≤ c / j := by
    calc 1 / y ≤ 1 / (c⁻¹ * j) := by gcongr
      _ = c / j := by field_simp
  have hN : p / (4 * x) + p * q ≤ M ^ 2 * c / j + 4 * M ^ 2 * q := by
    have : p * q ≤ 4 * M ^ 2 * q := mul_le_mul_of_nonneg_right hp4 hq
    linarith
  have hMc : 0 ≤ M ^ 2 * c := mul_nonneg (sq_nonneg M) hc.le
  have hN0 : 0 ≤ M ^ 2 * c / j + 4 * M ^ 2 * q :=
    add_nonneg (div_nonneg hMc hj.le) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hq)
  have h3 : (p / (4 * x) + p * q) / y ≤ (M ^ 2 * c / j + 4 * M ^ 2 * q) * (c / j) := by
    calc (p / (4 * x) + p * q) / y = (p / (4 * x) + p * q) * (1 / y) := by ring
      _ ≤ (M ^ 2 * c / j + 4 * M ^ 2 * q) * (c / j) :=
          mul_le_mul hN h2 (one_div_pos.mpr hy0).le hN0
  have h4 : (M ^ 2 * c / j + 4 * M ^ 2 * q) * (c / j)
      = M ^ 2 * c ^ 2 / j ^ 2 + 2 * c * M ^ 2 * (2 * q / j) := by
    field_simp
    ring
  have h5 : 2 * q / j ≤ q ^ 2 + 1 / j ^ 2 := by
    have e1 : 2 * q / j = 2 * (q * (1 / j)) := by ring
    have e2 : (1 : ℝ) / j ^ 2 = (1 / j) ^ 2 := by rw [one_div_pow]
    rw [e1, e2]
    nlinarith [sq_nonneg (q - 1 / j)]
  have hβ : 0 ≤ 2 * c * M ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hc.le) (sq_nonneg M)
  have h6 : 2 * c * M ^ 2 * (2 * q / j) ≤ 2 * c * M ^ 2 * (q ^ 2 + 1 / j ^ 2) :=
    mul_le_mul_of_nonneg_left h5 hβ
  calc (p / (4 * x) + p * q) / y ≤ (M ^ 2 * c / j + 4 * M ^ 2 * q) * (c / j) := h3
    _ = M ^ 2 * c ^ 2 / j ^ 2 + 2 * c * M ^ 2 * (2 * q / j) := h4
    _ ≤ M ^ 2 * c ^ 2 / j ^ 2 + 2 * c * M ^ 2 * (q ^ 2 + 1 / j ^ 2) := by linarith [h6]
    _ = (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) / j ^ 2 + 2 * c * M ^ 2 * q ^ 2 := by ring

/-- Symmetric product bound from an absolutely summable majorant of `G - 1`. -/
theorem g3007_prod_bound (G : ℤ → ℂ) (maj : ℤ → ℝ) (hmaj : Summable maj)
    (hG : ∀ k, ‖G k - 1‖ ≤ maj k) (K : ℝ) (hK : ∑' k, maj k ≤ K) :
    ‖∏'[symmetricIcc ℤ] k, G k‖ ≤ Real.exp K := by
  have hs : Summable fun k => ‖G k - 1‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hG hmaj
  have hsum : ∑' k, ‖G k - 1‖ ≤ K := (Summable.tsum_le_tsum hG hs hmaj).trans hK
  have e : ∏'[symmetricIcc ℤ] k, G k = ∏'[symmetricIcc ℤ] k, (1 + (G k - 1)) := by
    congr 1
    funext k
    ring
  rw [e, Lib.tprod_symm_eq_tprod_of_summable hs]
  exact (Lib.norm_tprod_one_add_le hs).trans (Real.exp_le_exp.mpr hsum)

/-- Transfer of the subtype l2 mass to a summable family indexed by `ℤ`. -/
theorem g3007_sum_transfer (n : ℤ) (A : P2Space38 n)
    (hs : Summable fun k : P2Index38 n => ‖A k‖ ^ 2) :
    Summable (fun k : ℤ => if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) ∧
      ∑' k : ℤ, (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) = ∑' x : P2Index38 n, ‖A x‖ ^ 2 := by
  have hinj : Function.Injective (Subtype.val : P2Index38 n → ℤ) := Subtype.val_injective
  have hF' : (fun k : ℤ => if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) ∘ (Subtype.val : P2Index38 n → ℤ)
      = fun x => ‖A x‖ ^ 2 := by
    funext x
    simp only [Function.comp_apply]
    rw [dif_pos x.2]
  have hzero : ∀ k ∉ Set.range (Subtype.val : P2Index38 n → ℤ),
      (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) = 0 := by
    intro k hk
    have hkn : ¬ (k ≠ n) := fun h => hk ⟨⟨k, h⟩, rfl⟩
    rw [dif_neg hkn]
  have hsumF : Summable (fun k : ℤ => if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) :=
    (hinj.summable_iff hzero).1 (by rw [hF']; exact hs)
  refine ⟨hsumF, ?_⟩
  have htsum := hinj.tsum_eq (f := fun k : ℤ => if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0)
    (by
      intro k hk
      by_contra hk'
      exact hk (hzero k hk'))
  rw [← htsum]
  exact tsum_congr fun x => by rw [dif_pos x.2]

/-- Lower bound for the standard root at a far index, uniform on the closed disc of `m`. -/
theorem g3007_lower (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R)
    (M : ℝ) (hM : 0 ≤ M) (hRM : ∀ k : ℤ, R k ≤ M) (m k : ℤ) (hmk : m ≠ k)
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) :
    c⁻¹ * |((m - k : ℤ) : ℝ)| ≤ ‖standardRoot φ k z‖ := by
  have hseg : segment ℝ (lamMinus φ k) (lamPlus φ k) ⊆ ball (C k) (R k) := (hsp.1 k).1
  have h := (g2019_root_sep_core C R c N hg M hM hRM hmk (lamMinus φ k) (lamPlus φ k) hseg z hz).1
  rw [g2019_standardRoot_pair φ hφ k z]
  exact h

/-- The gap of a fixed index is bounded by the radius bound. -/
theorem g3007_gamma_le (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hsp : IsolatingSpectral38 φ C R) (M : ℝ) (hRM : ∀ k : ℤ, R k ≤ M) (k : ℤ) :
    ‖gamma2 φ k‖ ≤ 4 * M ^ 2 := by
  have hγ : gamma2 φ k = (lamPlus φ k - lamMinus φ k) ^ 2 :=
    gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ hφ k
  have hseg : segment ℝ (lamMinus φ k) (lamPlus φ k) ⊆ ball (C k) (R k) := (hsp.1 k).1
  have hb : lamPlus φ k ∈ ball (C k) (R k) := hseg (right_mem_segment ℝ _ _)
  have ha : lamMinus φ k ∈ ball (C k) (R k) := hseg (left_mem_segment ℝ _ _)
  rw [mem_ball] at ha hb
  have hd : ‖lamPlus φ k - lamMinus φ k‖ ≤ 2 * M := by
    rw [← dist_eq_norm]
    have h1 := dist_triangle_right (lamPlus φ k) (lamMinus φ k) (C k)
    have := hRM k
    linarith
  have h0 : 0 ≤ ‖lamPlus φ k - lamMinus φ k‖ := norm_nonneg _
  rw [hγ, norm_pow]
  calc ‖lamPlus φ k - lamMinus φ k‖ ^ 2
      = ‖lamPlus φ k - lamMinus φ k‖ * ‖lamPlus φ k - lamMinus φ k‖ := sq _
    _ ≤ (2 * M) * (2 * M) := mul_le_mul hd hd h0 (by linarith)
    _ = 4 * M ^ 2 := by ring

/-- Per-index estimate: the ratio error is bounded by the majorant, uniformly in `n`. -/
theorem g3007_term (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R)
    (M : ℝ) (hM : 0 ≤ M) (hRM : ∀ k : ℤ, R k ≤ M) (m k : ℤ) (hmk : m ≠ k)
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) (A : ℂ) :
    ‖(tauN φ k + gamma2 φ k * A - z) / standardRoot φ k z - 1‖ ≤
      (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (1 / ((m - k : ℤ) : ℝ) ^ 2) + 2 * c * M ^ 2 * ‖A‖ ^ 2 := by
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hjne : ((m - k : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hmk)
  have hj : 0 < |((m - k : ℤ) : ℝ)| := abs_pos.mpr hjne
  have hτ : tauN φ k = (lamPlus φ k + lamMinus φ k) / 2 :=
    tau_pair_mean38 discC discR isolating_selectors_admissible38 φ hφ k
  have hmid : (lamMinus φ k + lamPlus φ k) / 2 ∈ ball (C k) (R k) :=
    (hsp.1 k).1 (stdRoot_midpoint_mem38 (lamMinus φ k) (lamPlus φ k))
  have hτmem : tauN φ k ∈ ball (C k) (R k) := by
    rw [hτ, show (lamPlus φ k + lamMinus φ k) / 2 = (lamMinus φ k + lamPlus φ k) / 2 by ring]
    exact hmid
  have hdist := g2019_closed_ball_dist C R c N hg hz hτmem
  have hgeo := (hg.2.2.2.1 m k hmk).1
  have hu_lb : c⁻¹ * |((m - k : ℤ) : ℝ)| ≤ ‖tauN φ k - z‖ := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hgeo.trans hdist
  have hw_lb := g3007_lower φ hφ C R c N hg hsp M hM hRM m k hmk z hz
  have hcj : 0 < c⁻¹ * |((m - k : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc0) hj
  have hu0 : tauN φ k - z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu_lb
    linarith
  have hw0 : standardRoot φ k z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw_lb
    linarith
  have hratio := g3007_ratio_error (τ := tauN φ k) (g := gamma2 φ k) (A := A) (z := z)
    (w := standardRoot φ k z) rfl hu0 hw0
  have hreal := g3007_real_bound (x := ‖tauN φ k - z‖) (y := ‖standardRoot φ k z‖)
    (p := ‖gamma2 φ k‖) (q := ‖A‖) (j := |((m - k : ℤ) : ℝ)|) hc0 hM hj hu_lb hw_lb
    (norm_nonneg _) (g3007_gamma_le φ hφ C R hsp M hRM k) (norm_nonneg _)
  have hsq : |((m - k : ℤ) : ℝ)| ^ 2 = ((m - k : ℤ) : ℝ) ^ 2 := sq_abs _
  calc ‖(tauN φ k + gamma2 φ k * A - z) / standardRoot φ k z - 1‖
      ≤ (‖gamma2 φ k‖ / (4 * ‖tauN φ k - z‖) + ‖gamma2 φ k‖ * ‖A‖) / ‖standardRoot φ k z‖ := hratio
    _ ≤ (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) / |((m - k : ℤ) : ℝ)| ^ 2 + 2 * c * M ^ 2 * ‖A‖ ^ 2 := hreal
    _ = (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (1 / ((m - k : ℤ) : ℝ) ^ 2) + 2 * c * M ^ 2 * ‖A‖ ^ 2 := by
      rw [hsq]
      ring

/-- Generic reindexing `k ↦ m - k` on `ℤ` for a summable real function. -/
theorem g3007_reflect {f : ℤ → ℝ} (hf : Summable f) (m : ℤ) :
    Summable (fun k : ℤ => f (m - k)) ∧ ∑' k : ℤ, f (m - k) = ∑' j : ℤ, f j :=
  ⟨(Equiv.subLeft m).summable_iff.mpr hf, (Equiv.subLeft m).tsum_eq f⟩

/-- Majorant sum over `ℤ`: `∑ (α/(m-k)^2 + β a_k)` is summable and bounded by `α S0 + β B`. -/
theorem g3007_maj_sum (m : ℤ) (a : ℤ → ℝ) (ha : Summable a) (α β : ℝ) (hβ : 0 ≤ β) (B : ℝ)
    (hB : ∑' k, a k ≤ B) :
    Summable (fun k : ℤ => α * (1 / ((m - k : ℤ) : ℝ) ^ 2) + β * a k) ∧
      ∑' k : ℤ, (α * (1 / ((m - k : ℤ) : ℝ) ^ 2) + β * a k)
        ≤ α * (∑' j : ℤ, 1 / (j : ℝ) ^ 2) + β * B := by
  have hf0 : Summable (fun j : ℤ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)
  obtain ⟨hD, hDsum⟩ := g3007_reflect hf0 m
  have hDα : Summable (fun k : ℤ => α * (1 / ((m - k : ℤ) : ℝ) ^ 2)) := hD.mul_left α
  have hAβ : Summable (fun k : ℤ => β * a k) := ha.mul_left β
  refine ⟨hDα.add hAβ, ?_⟩
  rw [Summable.tsum_add hDα hAβ, tsum_mul_left, tsum_mul_left, hDsum]
  have h3 := mul_le_mul_of_nonneg_left hB hβ
  linarith

/-- Double-product bound, uniform in `n` and `m`, with the majorant summed over `ℤ`. -/
theorem g3007_double_bound (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R)
    (M : ℝ) (hM : 0 ≤ M) (hRM : ∀ k : ℤ, R k ≤ M) (B : ℝ) (n m : ℤ) (hmn : m ≠ n)
    (z : ℂ) (hz : z ∈ closedBall (C m) (R m)) (A : P2Space38 n)
    (hfac : ∀ k : P2Index38 n, normalizedRoot n k.1 φ = tauN φ k.1 + gamma2 φ k.1 * A k)
    (hs : Summable fun k : P2Index38 n => ‖A k‖ ^ 2)
    (hle : ∑' k : P2Index38 n, ‖A k‖ ^ 2 ≤ B) :
    ‖doubleRootRatio φ (p2Extend38 n (sourceF n φ)) n m z‖ ≤
      Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2) + 2 * c * M ^ 2 * B) := by
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  obtain ⟨hsum, hsumeq⟩ := g3007_sum_transfer n A hs
  have hβ : 0 ≤ 2 * c * M ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hc0.le) (sq_nonneg M)
  have hα : 0 ≤ c ^ 2 * M ^ 2 + 2 * c * M ^ 2 :=
    add_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg M)) hβ
  have hB' : ∑' k : ℤ, (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) ≤ B := by
    rw [hsumeq]
    exact hle
  have hmaj := g3007_maj_sum m (fun k : ℤ => if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) hsum
    (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) (2 * c * M ^ 2) hβ B hB'
  have hmaj0 : ∀ k : ℤ, 0 ≤ (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (1 / ((m - k : ℤ) : ℝ) ^ 2) +
      2 * c * M ^ 2 * (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) := by
    intro k
    have hk1 : 0 ≤ 1 / ((m - k : ℤ) : ℝ) ^ 2 := by positivity
    have hk2 : 0 ≤ (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) := by
      by_cases hkn : k ≠ n
      · rw [dif_pos hkn]
        positivity
      · rw [dif_neg hkn]
    exact add_nonneg (mul_nonneg hα hk1) (mul_nonneg hβ hk2)
  have hterm : ∀ k : ℤ,
      ‖(if k = n ∨ k = m then (1 : ℂ)
        else (Lib.sigmaOf (p2Extend38 n (sourceF n φ)) k - z) / standardRoot φ k z) - 1‖ ≤
        (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (1 / ((m - k : ℤ) : ℝ) ^ 2) +
          2 * c * M ^ 2 * (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) := by
    intro k
    by_cases hk : k = n ∨ k = m
    · rw [if_pos hk, sub_self, norm_zero]
      exact hmaj0 k
    · rw [if_neg hk]
      push_neg at hk
      obtain ⟨hkn, hkm⟩ := hk
      have hσ0 := g2075_root_eq_sigma n k φ hkn
      have hf : normalizedRoot n k φ = tauN φ k + gamma2 φ k * A ⟨k, hkn⟩ := hfac ⟨k, hkn⟩
      have hσ : Lib.sigmaOf (p2Extend38 n (sourceF n φ)) k = tauN φ k + gamma2 φ k * A ⟨k, hkn⟩ :=
        hσ0.symm.trans hf
      have ha : (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0) = ‖A ⟨k, hkn⟩‖ ^ 2 := dif_pos hkn
      rw [hσ, ha]
      exact g3007_term φ hφ C R c N hg hsp M hM hRM m k (Ne.symm hkm) z hz (A ⟨k, hkn⟩)
  have hprod := g3007_prod_bound
    (fun k : ℤ => if k = n ∨ k = m then (1 : ℂ)
      else (Lib.sigmaOf (p2Extend38 n (sourceF n φ)) k - z) / standardRoot φ k z)
    (fun k : ℤ => (c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (1 / ((m - k : ℤ) : ℝ) ^ 2) +
      2 * c * M ^ 2 * (if h : k ≠ n then ‖A ⟨k, h⟩‖ ^ 2 else 0))
    hmaj.1 hterm _ hmaj.2
  unfold doubleRootRatio
  exact hprod

/-- **G3-007 bound support (STOP item 2).** Uniform bound on `psiZeta` over a neighbourhood of `φ0`. -/
theorem G3_007_bound (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ∃ V : Set PotPair, ∃ C : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧ 0 < C ∧
      ∀ φ ∈ V, IsolatingFamily38 φ (discC φ0) (discR φ0) ∧
        ∀ n m : ℤ, m ≠ n → ∀ z ∈ Metric.closedBall (discC φ0 m) (discR φ0 m),
          ‖psiZeta φ (p2Extend38 n (sourceF n φ)) n m z‖ ≤ C * Lib.c3w n m := by
  have hgk0 : φ0 ∈ gkW := G2_075.2.2.1 hφ0
  obtain ⟨ρ, hρ, c, N, hg, hsp⟩ :=
    fixed_family_persistence38 φ0 (discC φ0) (discR φ0) (isolating_family38 φ0 hgk0)
  obtain ⟨M, hM, hRM⟩ := g2019_radius_bound (discC φ0) (discR φ0) c N hg
  obtain ⟨V2, hV2o, hφ0V2, hV2W, B, hB, hA⟩ := G2_074 φ0 hφ0
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  refine ⟨ball φ0 ρ ∩ V2,
    c * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
      + 2 * c * M ^ 2 * B),
    isOpen_ball.inter hV2o, ⟨mem_ball_self hρ, hφ0V2⟩, inter_subset_right.trans hV2W,
    mul_pos hc0 (Real.exp_pos _), ?_⟩
  rintro φ ⟨hφρ, hφV2⟩
  refine ⟨⟨c, N, hg, hsp φ hφρ⟩, ?_⟩
  intro n m hmn z hz
  have hφgk : φ ∈ gkW := G2_075.2.2.1 (hV2W hφV2)
  obtain ⟨A, hfac, hs, hle⟩ := hA φ hφV2 n
  have hD := g3007_double_bound φ hφgk (discC φ0) (discR φ0) c N hg (hsp φ hφρ) M hM hRM B
    n m hmn z hz A hfac hs hle
  have hw := g3007_lower φ hφgk (discC φ0) (discR φ0) c N hg (hsp φ hφρ) M hM hRM m n hmn z hz
  have hj : 0 < |((m - n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (sub_ne_zero.mpr hmn))
  have hpos : 0 < ‖standardRoot φ n z‖ := lt_of_lt_of_le (mul_pos (inv_pos.mpr hc0) hj) hw
  have hc3 : 1 / ‖standardRoot φ n z‖ ≤ c * Lib.c3w n m := by
    have e : Lib.c3w n m = 1 / |((m - n : ℤ) : ℝ)| := by
      unfold Lib.c3w
      push_cast
      rfl
    rw [e]
    calc 1 / ‖standardRoot φ n z‖ ≤ 1 / (c⁻¹ * |((m - n : ℤ) : ℝ)|) :=
          one_div_le_one_div_of_le (mul_pos (inv_pos.mpr hc0) hj) hw
      _ = c * (1 / |((m - n : ℤ) : ℝ)|) := by
          field_simp
  have hc3nn : 0 ≤ c * Lib.c3w n m := by
    refine mul_nonneg hc0.le ?_
    unfold Lib.c3w
    positivity
  unfold psiZeta
  rw [norm_mul, norm_div, Complex.norm_I]
  calc 1 / ‖standardRoot φ n z‖ * ‖doubleRootRatio φ (p2Extend38 n (sourceF n φ)) n m z‖
      ≤ (c * Lib.c3w n m) * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
          + 2 * c * M ^ 2 * B) :=
        mul_le_mul hc3 hD (norm_nonneg _) hc3nn
    _ = c * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
          + 2 * c * M ^ 2 * B) * Lib.c3w n m := by ring


/-- Domain membership: for `z` in the open disc of `m`, the spectral segments of every `k ≠ m` avoid `z`. -/
theorem g3007_domain (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R) (m : ℤ) (z : ℂ)
    (hz : z ∈ ball (C m) (R m)) : (φ, z) ∈ a5OmittedRootDomain38 m := by
  refine ⟨hφ, fun k hk hseg => ?_⟩
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hwk : z ∈ ball (C k) (R k) := (hsp.1 k).1 hseg
  have h0 := g2019_closed_ball_dist C R c N hg (ball_subset_closedBall hz) hwk
  rw [dist_self] at h0
  have h1 := (hg.2.2.2.1 m k (Ne.symm hk)).1
  have hjne : ((m - k : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hk))
  have hpos : 0 < c⁻¹ * |((m - k : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc0) (abs_pos.mpr hjne)
  linarith

/-- Partial-product identity (as in G2-048): the omitted-`n` product equals `standardRoot n` times the
omitted-`m` ratio at the shifted sequence `s + (z - σ_n + 1) e_n`, for `z` in the `m`-domain. -/
theorem g3007_dr_identity (φ : PotPair) (n m : ℤ) (hmn : m ≠ n) (s : Lib.L2Seq) (z : ℂ)
    (hsn : standardRoot φ n z ≠ 0) (hp : (φ, z) ∈ a5OmittedRootDomain38 m) :
    doubleRootRatio φ s n m z =
      standardRoot φ n z * p2OmittedRatio38 m
        ((φ, s + (z - Lib.sigmaOf s n + 1) • lp.single 2 n (1 : ℂ)), z) := by
  have hnm : n ≠ m := fun h => hmn h.symm
  set c : ℂ := z - Lib.sigmaOf s n + 1 with hc
  set s' : Lib.L2Seq := s + c • lp.single 2 n (1 : ℂ) with hs'
  have hσn : Lib.sigmaOf s' n - z = 1 := by
    rw [hs', G2048Aux.sigma_shift_eq, hc]; ring
  have hp0 : ((φ, s'), z) ∈ {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} := hp
  have hT := ((G2_022 m).2.tendsto_at hp0)
  have hrel : ∀ᶠ N : ℕ in atTop,
      (∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
      standardRoot φ n z * ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k=m then (1 : ℂ) else (Lib.sigmaOf s' k-z)/standardRoot φ k z := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [← Finset.mul_prod_erase _ _ hn, ← Finset.mul_prod_erase _ _ hn]
    have e1 : (if n = n ∨ n = m then (1 : ℂ) else (Lib.sigmaOf s n-z)/standardRoot φ n z) = 1 := by
      simp
    have e2 : (if n = m then (1 : ℂ) else (Lib.sigmaOf s' n-z)/standardRoot φ n z) =
        (standardRoot φ n z)⁻¹ := by
      rw [if_neg hnm, hσn]; simp
    have e3 : ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (if k=m then (1 : ℂ) else (Lib.sigmaOf s' k-z)/standardRoot φ k z) := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := (Finset.mem_erase.1 hk).1
      by_cases hkm : k = m
      · simp [hkm]
      · rw [if_neg (by tauto), if_neg hkm, G2048Aux.sigma_shift_ne s n c k hkn]
    rw [e1, e2, e3]
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      atTop (𝓝 (standardRoot φ n z * p2OmittedRatio38 m ((φ, s'), z))) := by
    refine Tendsto.congr' (hrel.mono fun N h => h.symm) ?_
    exact hT.const_mul (standardRoot φ n z)
  have hHP : HasProd (fun k : ℤ => if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      (standardRoot φ n z * p2OmittedRatio38 m ((φ, s'), z)) (symmetricIcc ℤ) :=
    hasProd_symmetricIcc_iff.2 hlim
  exact hHP.tprod_eq

/-- Analyticity of `psiZeta` on the open disc of `m`, for `φ` in the gk family. -/
theorem g3007_analytic_ball (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R)
    (M : ℝ) (hM : 0 ≤ M) (hRM : ∀ k : ℤ, R k ≤ M) (n m : ℤ) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (fun z => psiZeta φ (p2Extend38 n (sourceF n φ)) n m z) (ball (C m) (R m)) := by
  set s : Lib.L2Seq := p2Extend38 n (sourceF n φ) with hs
  set v : Lib.L2Seq := lp.single 2 n (1 : ℂ) with hv
  set σ : ℂ := Lib.sigmaOf s n with hσ
  let P0 : (PotPair × Lib.L2Seq) × ℂ := ((φ, s - (σ - 1) • v), 0)
  let W : (PotPair × Lib.L2Seq) × ℂ := ((0, v), 1)
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => ((φ, s + (z - σ + 1) • v), z)) (ball (C m) (R m)) := by
    have e : (fun z : ℂ => ((φ, s + (z - σ + 1) • v), z)) = fun z : ℂ => P0 + z • W := by
      funext z
      have hs2 : s + (z - σ + 1) • v = s - (σ - 1) • v + z • v := by module
      simp only [P0, W, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, zero_add, smul_eq_mul,
        mul_one, hs2]
    rw [e]
    intro z _
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hMaps : Set.MapsTo (fun z : ℂ => ((φ, s + (z - σ + 1) • v), z)) (ball (C m) (R m))
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} := fun z hz =>
    g3007_domain φ hφ C R c N hg hsp m z hz
  have hcomp := (G2_022 m).1.comp hF hMaps
  have hid : ∀ z ∈ ball (C m) (R m),
      psiZeta φ s n m z = Complex.I * (p2OmittedRatio38 m ∘ fun z : ℂ => ((φ, s + (z - σ + 1) • v), z)) z := by
    intro z hz
    have hzc : z ∈ closedBall (C m) (R m) := ball_subset_closedBall hz
    have hsn : standardRoot φ n z ≠ 0 := by
      have hlow := g3007_lower φ hφ C R c N hg hsp M hM hRM m n hmn z hzc
      have hj : 0 < |((m - n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (sub_ne_zero.mpr hmn))
      have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
      intro h
      rw [h, norm_zero] at hlow
      have : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc0) hj
      linarith
    have hdom := g3007_domain φ hφ C R c N hg hsp m z hz
    unfold psiZeta
    rw [g3007_dr_identity φ n m hmn s z hsn hdom, hσ]
    simp only [Function.comp_apply]
    field_simp
    rw [hv]
  have hgoal : AnalyticOnNhd ℂ (fun z => Complex.I * (p2OmittedRatio38 m ∘ fun z : ℂ =>
      ((φ, s + (z - σ + 1) • v), z)) z) (ball (C m) (R m)) :=
    analyticOnNhd_const.mul hcomp
  exact AnalyticOnNhd.congr isOpen_ball hgoal (fun z hz => (hid z hz).symm)

/-- **G3-007 (followup5 STATEMENTS/G3.md), verbatim head.** Uses the landed `betaZeta` host (G3ZetaHost). -/
theorem G3_007 (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
  ∃ V : Set PotPair, ∃ C : ℝ,
    IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧ 0 < C ∧
    ∀ φ ∈ V,
      IsolatingFamily38 φ (discC φ0) (discR φ0) ∧
      ∀ n m : ℤ, m ≠ n →
        AnalyticOnNhd ℂ (betaZeta n m φ) (ball (discC φ0 m) (discR φ0 m)) ∧
        ∀ z ∈ ball (discC φ0 m) (discR φ0 m),
          ‖betaZeta n m φ z‖ ≤ C * Lib.c3w n m := by
  have hgk0 : φ0 ∈ gkW := G2_075.2.2.1 hφ0
  obtain ⟨ρ, hρ, c, N, hg, hsp⟩ :=
    fixed_family_persistence38 φ0 (discC φ0) (discR φ0) (isolating_family38 φ0 hgk0)
  obtain ⟨M, hM, hRM⟩ := g2019_radius_bound (discC φ0) (discR φ0) c N hg
  obtain ⟨V2, hV2o, hφ0V2, hV2W, B, hB, hA⟩ := G2_074 φ0 hφ0
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  refine ⟨ball φ0 ρ ∩ V2,
    c * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
      + 2 * c * M ^ 2 * B),
    isOpen_ball.inter hV2o, ⟨mem_ball_self hρ, hφ0V2⟩, inter_subset_right.trans hV2W,
    mul_pos hc0 (Real.exp_pos _), ?_⟩
  rintro φ ⟨hφρ, hφV2⟩
  have hφgk : φ ∈ gkW := G2_075.2.2.1 (hV2W hφV2)
  refine ⟨⟨c, N, hg, hsp φ hφρ⟩, fun n m hmn => ⟨?_, fun z hz => ?_⟩⟩
  · exact g3007_analytic_ball φ hφgk (discC φ0) (discR φ0) c N hg (hsp φ hφρ) M hM hRM n m hmn
  · have hzc : z ∈ closedBall (discC φ0 m) (discR φ0 m) := ball_subset_closedBall hz
    obtain ⟨A, hfac, hs, hle⟩ := hA φ hφV2 n
    have hD := g3007_double_bound φ hφgk (discC φ0) (discR φ0) c N hg (hsp φ hφρ) M hM hRM B
      n m hmn z hzc A hfac hs hle
    have hw := g3007_lower φ hφgk (discC φ0) (discR φ0) c N hg (hsp φ hφρ) M hM hRM m n hmn z hzc
    have hj : 0 < |((m - n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (sub_ne_zero.mpr hmn))
    have hpos : 0 < ‖standardRoot φ n z‖ := lt_of_lt_of_le (mul_pos (inv_pos.mpr hc0) hj) hw
    have hc3 : 1 / ‖standardRoot φ n z‖ ≤ c * Lib.c3w n m := by
      have e : Lib.c3w n m = 1 / |((m - n : ℤ) : ℝ)| := by
        unfold Lib.c3w
        push_cast
        rfl
      rw [e]
      calc 1 / ‖standardRoot φ n z‖ ≤ 1 / (c⁻¹ * |((m - n : ℤ) : ℝ)|) :=
            one_div_le_one_div_of_le (mul_pos (inv_pos.mpr hc0) hj) hw
        _ = c * (1 / |((m - n : ℤ) : ℝ)|) := by
            field_simp
    have hc3nn : 0 ≤ c * Lib.c3w n m := by
      refine mul_nonneg hc0.le ?_
      unfold Lib.c3w
      positivity
    unfold betaZeta psiZeta
    rw [norm_mul, norm_div, Complex.norm_I]
    calc 1 / ‖standardRoot φ n z‖ * ‖doubleRootRatio φ (p2Extend38 n (sourceF n φ)) n m z‖
        ≤ (c * Lib.c3w n m) * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
            + 2 * c * M ^ 2 * B) :=
          mul_le_mul hc3 hD (norm_nonneg _) hc3nn
      _ = c * Real.exp ((c ^ 2 * M ^ 2 + 2 * c * M ^ 2) * (∑' j : ℤ, 1 / (j : ℝ) ^ 2)
            + 2 * c * M ^ 2 * B) * Lib.c3w n m := by ring
end
end NlsGge.GKDefinitionDesign
