import Mathlib
import QuantumNLS.RB01RootPrep
import QuantumNLS.RootGapLevelSets
import QuantumNLS.DEF014Phase

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-13: the two-root count, the symmetric functions and the
Cauchy quotient on the real slice (source `collective_actions.tex:369-428`: "Rouché's theorem on |w| = 3d and on
|w| = d/8 shows that f_n has exactly two zeros, counted with multiplicity, in the larger disk, and both lie in the
smaller disk"; eq. `GB01-H`, eq. `GB01-factor`, eq. `GB01-H-bound`).  Actual DEF-014 objects, `κ > 0`.

**Recorded proof-route deviation (integrator decision, 2026-11-16; statement unchanged).**  On the real slice,
Rouché's theorem and the argument-principle count of source :369-375 are replaced by
(i) phase labels at `p_n ± d`: along `s ↦ s·u`, `s ∈ [0,1]`, the points `p_n ± d` are band points
(`RB01RootPrep.root_prep` (d)), the boundary phase is continuous there in the field
(`DEF014Phase.continuous_phase_at_band`), never an integer multiple of `π` at a band point
(`RootGapLevelSets.two_le_abs`), and equals the free value `L x / 2 = nπ ± 1/8` at `s = 0`
(`PhysicalContinuousBoundary.boundary_zero`); the intermediate value theorem gives
`phase(p_n − d) ∈ ((n−1)π, nπ)` and `phase(p_n + d) ∈ (nπ, (n+1)π)`;
(ii) the exact two-root count: zeros of `f_n` in `|w| ≤ 4d` are real (`RootGapMultiplicity.zeros_real'`), lie in
`|w| < d/8` (`root_prep` (b)), have boundary phase `kπ` (`RootGapMultiplicity.zero_data`), hence `k = n` by
monotonicity and (i), hence lie in the level set `{θ = nπ} = [b⁻, b⁺]` (`RootGapLevelSets.level_interval`), whose
interior is a strict gap (`RootGapLevelSets.level_dichotomy`); multiplicities are `(1,1)` at `b⁻ < b⁺` or `2` at
`b⁻ = b⁺` (`level_dichotomy`, the order cases of `RootGapMultiplicity`, `order_sq_sub`).
The root symmetric functions are therefore defined here from `b^±` directly; the contour-integral moments
`s_{1,2}` on the complexification and their identification on the real slice are the next stage.

* `bm`, `bp`: `b^± = inf/sup {θ = nπ}`; `alpha = (b⁻ + b⁺)/2 − p_n`, `tau = ((b⁺ − b⁻)/2)²`,
  `Pn w = (w − α)² − τ = (w − (b⁻ − p_n))(w − (b⁺ − p_n))`;
* `Hn w = (2πi)⁻¹ ∮_{|ξ| = 3d} (ξ − w)⁻¹ f_n(ξ)/P_n(ξ) dξ` (eq. `GB01-H`);
* **`root_count`**: for every `u₀` there are `N`, `ρ > 0` such that for `|n| > N`, `‖u − u₀‖ < ρ`, `t ∈ [0,1]`,
  `q = t·u`: the phase labels; `{θ = nπ} = [b⁻, b⁺]`, `|b^± − p_n| < d/8`; for `|w| ≤ 4d`,
  `f_n(w) = 0 ↔ w ∈ {b⁻ − p_n, b⁺ − p_n}`; total multiplicity two (orders of `Δ² − 4` at `b^±`);
  `f_n = P_n H_n` on `|w| < 3d` (eq. `GB01-factor`), `H_n` holomorphic there, and `|H_n + L²| < L²/4` on
  `|w| ≤ 2d` (eq. `GB01-H-bound`; in fact `≤ L²/5` on `|w| < 3d`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric

namespace QuantumNLS.RB01RootCount

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootPrep (fn freeF dd ε₀ dd_pos root_prep)
open QuantumNLS.PhysicalContinuousBoundary (boundary boundary_zero monotone_all)
open QuantumNLS.RootGapMultiplicity (Dl sgn sgn_sq sgn_cases zeros_real' hD hreal ray_of_boundary order_sq_sub
  zero_data)
open QuantumNLS.RootGapLevelSets (lev level_interval level_dichotomy two_le_abs boundary_eq_of_level)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ## The level set `{θ = nπ} = [b⁻, b⁺]` -/

/-- `b⁻_n`. -/
def bm (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℝ := sInf (lev hκ q n)

/-- `b⁺_n`. -/
def bp (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℝ := sSup (lev hκ q n)

theorem lev_eq (hκ : 0 < κ) (q : L2T L) (n : ℤ) :
    bm hκ q n ≤ bp hκ q n ∧ lev hκ q n = Icc (bm hκ q n) (bp hκ q n) := by
  obtain ⟨a, b, hab, h⟩ := level_interval hκ q n
  have h1 : bm hκ q n = a := by unfold bm; rw [h, csInf_Icc hab]
  have h2 : bp hκ q n = b := by unfold bp; rw [h, csSup_Icc hab]
  rw [h1, h2]; exact ⟨hab, h⟩

/-! ## Phase labels at `p_n ± d` -/

theorem not_level_of_band (hκ : 0 < κ) (q : L2T L) {x : ℝ} (hx : |(Dl κ q (x : ℂ)).re| < 2) (k : ℤ) :
    (boundary hκ q x).re ≠ (k : ℝ) * Real.pi := by
  intro h
  have := two_le_abs hκ q (n := k) (x := x) h
  linarith

theorem free_phase (hκ : 0 < κ) (n : ℤ) (s : ℝ) :
    (boundary hκ (0 : L2T L) (QuantumNLS.LocalSpectral.pm L n + s * dd L)).re = (n : ℝ) * Real.pi + s / 8 := by
  have hL : 0 < L := Fact.out
  rw [boundary_zero]
  have e : (L : ℂ) * ((QuantumNLS.LocalSpectral.pm L n + s * dd L : ℝ) : ℂ) / 2 =
      ((L * (QuantumNLS.LocalSpectral.pm L n + s * dd L) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.ofReal_re]
  unfold QuantumNLS.LocalSpectral.pm dd
  field_simp
  ring

theorem path_label {g : ℝ → ℝ} (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt g t) {a b : ℝ}
    (h0 : g 0 ∈ Ioo a b) (ha : ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ a) (hb : ∀ t ∈ Icc (0 : ℝ) 1, g t ≠ b) :
    ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Ioo a b := by
  intro t ht
  have hcon : ContinuousOn g (Icc 0 t) := fun s hs =>
    (hc s ⟨hs.1, hs.2.trans ht.2⟩).continuousWithinAt
  refine ⟨?_, ?_⟩
  · by_contra hle
    push_neg at hle
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc' ht.1 hcon ⟨hle, h0.1.le⟩
    exact ha s ⟨hs.1, hs.2.trans ht.2⟩ hgs
  · by_contra hle
    push_neg at hle
    obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc ht.1 hcon ⟨h0.2.le, hle⟩
    exact hb s ⟨hs.1, hs.2.trans ht.2⟩ hgs

theorem phase_continuousAt (hκ : 0 < κ) (u : L2T L) {x t : ℝ}
    (hx : ‖Dl κ (t • u) (x : ℂ)‖ < 2) :
    ContinuousAt (fun s : ℝ => (boundary hκ (s • u) x).re) t := by
  have hφ : Continuous (fun s : ℝ => ((⟨κ, hκ⟩ : {κ : ℝ // 0 < κ}), s • u)) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have h := QuantumNLS.DEF014Phase.continuous_phase_at_band (L := L) (⟨κ, hκ⟩, t • u) (x := x)
    (lt_of_le_of_lt (Complex.abs_re_le_norm _) hx)
  exact ContinuousAt.comp (g := fun p : QuantumNLS.DEF014Phase.Param L => QuantumNLS.DEF014Phase.phase p x)
    (f := fun s : ℝ => ((⟨κ, hκ⟩ : {κ : ℝ // 0 < κ}), s • u)) (x := t) h hφ.continuousAt

theorem labels (hκ : 0 < κ) (u : L2T L) (n : ℤ)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (t • u) ((QuantumNLS.LocalSpectral.pm L n - dd L : ℝ) : ℂ)‖ < 2)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (t • u) ((QuantumNLS.LocalSpectral.pm L n + dd L : ℝ) : ℂ)‖ < 2) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (boundary hκ (t • u) (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
          Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi) ∧
      (boundary hκ (t • u) (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
          Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi) := by
  have hπ := Real.pi_gt_three
  intro t ht
  constructor
  · refine path_label (g := fun s : ℝ => (boundary hκ (s • u) (QuantumNLS.LocalSpectral.pm L n - dd L)).re)
      (fun s hs => phase_continuousAt hκ u (hm s hs)) ?_ ?_ ?_ t ht
    · show (boundary hκ ((0 : ℝ) • u) _).re ∈ _
      rw [zero_smul, show QuantumNLS.LocalSpectral.pm L n - dd L =
        QuantumNLS.LocalSpectral.pm L n + (-1) * dd L by ring, free_phase]
      constructor <;> linarith
    · intro s hs h
      exact not_level_of_band hκ (s • u) (lt_of_le_of_lt (Complex.abs_re_le_norm _) (hm s hs)) (n - 1)
        (by rw [h]; push_cast; ring)
    · intro s hs h
      exact not_level_of_band hκ (s • u) (lt_of_le_of_lt (Complex.abs_re_le_norm _) (hm s hs)) n h
  · refine path_label (g := fun s : ℝ => (boundary hκ (s • u) (QuantumNLS.LocalSpectral.pm L n + dd L)).re)
      (fun s hs => phase_continuousAt hκ u (hp s hs)) ?_ ?_ ?_ t ht
    · show (boundary hκ ((0 : ℝ) • u) _).re ∈ _
      rw [zero_smul, show QuantumNLS.LocalSpectral.pm L n + dd L =
        QuantumNLS.LocalSpectral.pm L n + 1 * dd L by ring, free_phase]
      constructor <;> linarith
    · intro s hs h
      exact not_level_of_band hκ (s • u) (lt_of_le_of_lt (Complex.abs_re_le_norm _) (hp s hs)) n h
    · intro s hs h
      exact not_level_of_band hκ (s • u) (lt_of_le_of_lt (Complex.abs_re_le_norm _) (hp s hs)) (n + 1)
        (by rw [h]; push_cast; ring)

/-! ## The exact two-root count -/

theorem cell_count (hκ : 0 < κ) (q : L2T L) (n : ℤ)
    (hb : ∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 10 / 65536 ≤ ‖fn κ q n w‖)
    (hlm : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
          Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi))
    (hlp : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
          Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi)) :
    |bm hκ q n - QuantumNLS.LocalSpectral.pm L n| < dd L / 8 ∧
    |bp hκ q n - QuantumNLS.LocalSpectral.pm L n| < dd L / 8 ∧
    (∀ w : ℂ, ‖w‖ ≤ 4 * dd L → (fn κ q n w = 0 ↔
        w = ((bm hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ∨
        w = ((bp hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ))) ∧
    ((bm hκ q n < bp hκ q n ∧ analyticOrderAt (fun z => Dl κ q z ^ 2 - 4) (bm hκ q n : ℂ) = 1 ∧
        analyticOrderAt (fun z => Dl κ q z ^ 2 - 4) (bp hκ q n : ℂ) = 1) ∨
      (bm hκ q n = bp hκ q n ∧ analyticOrderAt (fun z => Dl κ q z ^ 2 - 4) (bm hκ q n : ℂ) = 2)) := by
  have hd := dd_pos (L := L)
  have hπ := Real.pi_pos
  obtain ⟨hle, hS⟩ := lev_eq hκ q n
  set p := QuantumNLS.LocalSpectral.pm L n with hp_def
  set a := bm hκ q n with ha_def
  set b := bp hκ q n with hb_def
  have mono := monotone_all hκ q
  have win : ∀ x ∈ lev hκ q n, p - dd L < x ∧ x < p + dd L := by
    intro x hx
    have hx' : (boundary hκ q x).re = (n : ℝ) * Real.pi := hx
    constructor
    · by_contra h
      push_neg at h
      have h' : (boundary hκ q x).re ≤ (boundary hκ q (p - dd L)).re := mono h
      linarith [hlm.2]
    · by_contra h
      push_neg at h
      have h' : (boundary hκ q (p + dd L)).re ≤ (boundary hκ q x).re := mono h
      linarith [hlp.1]
  have zero_of : ∀ x ∈ lev hκ q n, |(Dl κ q (x : ℂ)).re| ≤ 2 →
      Dl κ q (x : ℂ) ^ 2 - 4 = 0 ∧ Dl κ q (x : ℂ) = 2 * (sgn n : ℂ) := by
    intro x hx h2
    obtain ⟨hDx, -⟩ := ray_of_boundary hκ q x n (boundary_eq_of_level hκ q hx h2)
    refine ⟨?_, hDx⟩
    rw [hDx]
    have h1 : (sgn n : ℂ) ^ 2 = 1 := by exact_mod_cast sgn_sq n
    linear_combination 4 * h1
  have small : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → fn κ q n w = 0 → ‖w‖ < dd L / 8 := by
    intro w hw h0
    by_contra h
    push_neg at h
    have := hb w h hw
    rw [h0, norm_zero] at this
    norm_num at this
  have tr : ∀ x : ℝ, fn κ q n ((x - p : ℝ) : ℂ) = Dl κ q (x : ℂ) ^ 2 - 4 := by
    intro x
    unfold fn
    congr 3
    push_cast
    ring
  obtain ⟨ha2, hb2, hcase⟩ := level_dichotomy hκ q n hle hS
  have ha_lev : a ∈ lev hκ q n := by rw [hS]; exact left_mem_Icc.2 hle
  have hb_lev : b ∈ lev hκ q n := by rw [hS]; exact right_mem_Icc.2 hle
  obtain ⟨za, hDa⟩ := zero_of a ha_lev ha2
  obtain ⟨zb, hDb⟩ := zero_of b hb_lev hb2
  have near : ∀ x ∈ lev hκ q n, Dl κ q (x : ℂ) ^ 2 - 4 = 0 → |x - p| < dd L / 8 := by
    intro x hx hz
    have hw := win x hx
    have hn : ‖((x - p : ℝ) : ℂ)‖ = |x - p| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 : |x - p| ≤ 4 * dd L := by
      rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
    have := small _ (by rw [hn]; exact h4) (by rw [tr]; exact hz)
    rwa [hn] at this
  refine ⟨near a ha_lev za, near b hb_lev zb, ?_, ?_⟩
  · intro w hw
    constructor
    · intro h0
      have hsm := small w hw h0
      have hz : Dl κ q ((p : ℂ) + w) ^ 2 - 4 = 0 := h0
      have him : w.im = 0 := by
        have := zeros_real' hκ q hz
        simpa using this
      set x := p + w.re with hx
      have hxw : ((p : ℂ) + w) = (x : ℂ) := by
        apply Complex.ext <;> simp [hx, him]
      rw [hxw] at hz
      have hre : |w.re| < dd L / 8 := lt_of_le_of_lt (Complex.abs_re_le_norm w) hsm
      rw [abs_lt] at hre
      obtain ⟨k, hk⟩ := zero_data hκ q x hz
      have hθ : (boundary hκ q x).re = (k : ℝ) * Real.pi := by rw [hk]; simp
      have h1 : (boundary hκ q (p - dd L)).re ≤ (boundary hκ q x).re :=
        mono (show p - dd L ≤ x by rw [hx]; linarith [hre.1])
      have h2 : (boundary hκ q x).re ≤ (boundary hκ q (p + dd L)).re :=
        mono (show x ≤ p + dd L by rw [hx]; linarith [hre.2])
      rw [hθ] at h1 h2
      have hk1 : ((n : ℝ) - 1) < k := by
        by_contra h
        push_neg at h
        have := mul_le_mul_of_nonneg_right h hπ.le
        linarith [hlm.1]
      have hk2 : (k : ℝ) < n + 1 := by
        by_contra h
        push_neg at h
        have := mul_le_mul_of_nonneg_right h hπ.le
        linarith [hlp.2]
      have hkn : k = n := by
        have e1 : n - 1 < k := by exact_mod_cast hk1
        have e2 : k < n + 1 := by exact_mod_cast hk2
        omega
      subst hkn
      have hxl : x ∈ lev hκ q k := hθ
      rw [hS] at hxl
      have hwx : w = ((x - p : ℝ) : ℂ) := by apply Complex.ext <;> simp [hx, him]
      rcases hcase with ⟨hlt, hint, -, -⟩ | ⟨heq, -⟩
      · rcases eq_or_lt_of_le hxl.1 with h | h
        · left; rw [hwx, ← h]
        · rcases eq_or_lt_of_le hxl.2 with h' | h'
          · right; rw [hwx, h']
          · exfalso
            have hgt := hint x ⟨h, h'⟩
            have hr := hreal κ q x
            have hsq : (Dl κ q (x : ℂ)).re ^ 2 = 4 := by
              have := congrArg Complex.re hz
              simp [pow_two, Complex.mul_re, hr] at this
              nlinarith [this]
            nlinarith [sq_abs (Dl κ q (x : ℂ)).re, abs_nonneg (Dl κ q (x : ℂ)).re]
      · left
        rw [hwx]
        have : x = a := le_antisymm (by rw [heq]; exact hxl.2) hxl.1
        rw [this]
    · rintro (h | h)
      · rw [h, tr]; exact za
      · rw [h, tr]; exact zb
  · rcases hcase with ⟨hlt, -, h1, h2⟩ | ⟨heq, h2⟩
    · left
      refine ⟨hlt, ?_, ?_⟩
      · rw [order_sq_sub hκ q a (sgn_cases n) hDa]; exact h1
      · rw [order_sq_sub hκ q b (sgn_cases n) hDb]; exact h2
    · right
      refine ⟨heq, ?_⟩
      rw [order_sq_sub hκ q a (sgn_cases n) hDa]; exact h2

/-! ## Symmetric functions and the Cauchy quotient -/

/-- `α_n = (b⁻ + b⁺)/2 − p_n`. -/
def alpha (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℝ :=
  (bm hκ q n + bp hκ q n) / 2 - QuantumNLS.LocalSpectral.pm L n

/-- `τ_n = ((b⁺ − b⁻)/2)²`. -/
def tau (hκ : 0 < κ) (q : L2T L) (n : ℤ) : ℝ := ((bp hκ q n - bm hκ q n) / 2) ^ 2

/-- `𝒫_n(w) = (w − α_n)² − τ_n`. -/
def Pn (hκ : 0 < κ) (q : L2T L) (n : ℤ) (w : ℂ) : ℂ :=
  (w - (alpha hκ q n : ℂ)) ^ 2 - (tau hκ q n : ℂ)

/-- eq. `GB01-H`: `H_n(w) = (2πi)⁻¹ ∮_{|ξ| = 3d} (ξ − w)⁻¹ f_n(ξ)/𝒫_n(ξ) dξ`. -/
def Hn (hκ : 0 < κ) (q : L2T L) (n : ℤ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∮ ξ in C(0, 3 * dd L), (ξ - w)⁻¹ • (fn κ q n ξ / Pn hκ q n ξ)

theorem Pn_eq (hκ : 0 < κ) (q : L2T L) (n : ℤ) (w : ℂ) :
    Pn hκ q n w = (w - ((bm hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ)) *
      (w - ((bp hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ)) := by
  unfold Pn alpha tau
  push_cast
  ring

theorem deriv_zero_of_order_two {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀)
    (h : analyticOrderAt g z₀ = 2) : deriv g z₀ = 0 := by
  obtain ⟨k, hk, -, hev⟩ := (hg.analyticOrderAt_eq_natCast (n := 2)).1 (by exact_mod_cast h)
  rw [Filter.EventuallyEq.deriv_eq (f := fun z => (z - z₀) ^ 2 • k z) hev]
  have h1 := ((hasDerivAt_id z₀).sub_const z₀).pow 2
  have h2 := h1.smul hk.differentiableAt.hasDerivAt
  refine h2.deriv.trans ?_
  simp

theorem dslope_factor {F : ℂ → ℂ} (hF : Differentiable ℂ F) {β₁ β₂ : ℂ} (h1 : F β₁ = 0) (h2 : F β₂ = 0)
    (hd : β₁ = β₂ → deriv F β₁ = 0) :
    Differentiable ℂ (dslope (dslope F β₁) β₂) ∧
      ∀ w, F w = (w - β₁) * (w - β₂) * dslope (dslope F β₁) β₂ w := by
  have hd1 : Differentiable ℂ (dslope F β₁) :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hF.differentiableOn)
  have hd2 : Differentiable ℂ (dslope (dslope F β₁) β₂) :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hd1.differentiableOn)
  have hz : dslope F β₁ β₂ = 0 := by
    by_cases h : β₂ = β₁
    · rw [h, dslope_same]; exact hd h.symm
    · rw [dslope_of_ne _ h, slope_def_field, h1, h2]; simp
  refine ⟨hd2, fun w => ?_⟩
  have e1 := sub_smul_dslope F β₁ w
  have e2 := sub_smul_dslope (dslope F β₁) β₂ w
  rw [smul_eq_mul, h1, sub_zero] at e1
  rw [smul_eq_mul, hz, sub_zero] at e2
  rw [← e1, ← e2]
  ring

/-- The outer-circle estimate for the quotient, scale free in `x = Lξ`. -/
theorem sphere_bound {ξ β₁ β₂ F : ℂ} (hξ : ‖ξ‖ = 3 * dd L) (h1 : ‖β₁‖ ≤ dd L / 8) (h2 : ‖β₂‖ ≤ dd L / 8)
    (hF : ‖F - freeF L ξ‖ ≤ 6 * ε₀) :
    (ξ - β₁) * (ξ - β₂) ≠ 0 ∧ ‖F / ((ξ - β₁) * (ξ - β₂)) + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5 := by
  have hL : 0 < L := Fact.out
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have hnL : ‖(L : ℂ)‖ = L := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  set x : ℂ := (L : ℂ) * ξ with hx
  set γ₁ : ℂ := (L : ℂ) * β₁ with hγ₁
  set γ₂ : ℂ := (L : ℂ) * β₂ with hγ₂
  have hxn : ‖x‖ = 3 / 4 := by
    rw [hx, norm_mul, hnL, hξ]; unfold dd; field_simp
  have hg1 : ‖γ₁‖ ≤ 1 / 32 := by
    rw [hγ₁, norm_mul, hnL]
    calc L * ‖β₁‖ ≤ L * (dd L / 8) := by gcongr
      _ = 1 / 32 := by unfold dd; field_simp; ring
  have hg2 : ‖γ₂‖ ≤ 1 / 32 := by
    rw [hγ₂, norm_mul, hnL]
    calc L * ‖β₂‖ ≤ L * (dd L / 8) := by gcongr
      _ = 1 / 32 := by unfold dd; field_simp; ring
  have hs1 : 23 / 32 ≤ ‖x - γ₁‖ := by have := norm_sub_norm_le x γ₁; linarith
  have hs2 : 23 / 32 ≤ ‖x - γ₂‖ := by have := norm_sub_norm_le x γ₂; linarith
  set Q := (x - γ₁) * (x - γ₂) with hQ
  have hQn : 529 / 1024 ≤ ‖Q‖ := by
    rw [hQ, norm_mul]; nlinarith [norm_nonneg (x - γ₁), norm_nonneg (x - γ₂)]
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, norm_zero] at hQn; norm_num at hQn
  have hPQ : (ξ - β₁) * (ξ - β₂) = Q / (L : ℂ) ^ 2 := by
    rw [hQ, hx, hγ₁, hγ₂]; field_simp
  have hP0 : (ξ - β₁) * (ξ - β₂) ≠ 0 := by
    rw [hPQ]; exact div_ne_zero hQ0 (pow_ne_zero 2 hL')
  refine ⟨hP0, ?_⟩
  have hfree : freeF L ξ = 2 * Complex.cos x - 2 := by
    unfold freeF
    have : x = 2 * ((L : ℂ) * ξ / 2) := by rw [hx]; ring
    rw [this, Complex.cos_two_mul]; ring
  have hcos := Complex.cos_bound (x := x) (by rw [hxn]; norm_num)
  rw [hxn] at hcos
  have hc2 : ‖2 * (Complex.cos x - (1 - x ^ 2 / 2))‖ ≤ 2 * ((3 / 4) ^ 4 * (5 / 96)) := by
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [this]; linarith
  have hq : ‖Q - x ^ 2‖ ≤ 49 / 1024 := by
    have e : Q - x ^ 2 = -((γ₁ + γ₂) * x) + γ₁ * γ₂ := by rw [hQ]; ring
    rw [e]
    calc ‖-((γ₁ + γ₂) * x) + γ₁ * γ₂‖ ≤ ‖(γ₁ + γ₂) * x‖ + ‖γ₁ * γ₂‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_neg]
      _ ≤ (‖γ₁‖ + ‖γ₂‖) * ‖x‖ + ‖γ₁‖ * ‖γ₂‖ := by
          have := norm_add_le γ₁ γ₂
          rw [norm_mul (γ₁ + γ₂) x, norm_mul γ₁ γ₂]
          nlinarith [norm_nonneg x]
      _ ≤ (1 / 32 + 1 / 32) * (3 / 4) + (1 / 32) * (1 / 32) := by
          rw [hxn]
          gcongr
      _ = 49 / 1024 := by norm_num
  have hFn : ‖F - freeF L ξ‖ ≤ 6 / 65536 := by unfold ε₀ at hF; linarith
  have hnum : ‖F + Q‖ ≤ 6 / 65536 + 2 * ((3 / 4) ^ 4 * (5 / 96)) + 49 / 1024 := by
    have e : F + Q = (F - freeF L ξ) + 2 * (Complex.cos x - (1 - x ^ 2 / 2)) + (Q - x ^ 2) := by
      rw [hfree]; ring
    rw [e]
    linarith [norm_add₃_le (a := F - freeF L ξ) (b := 2 * (Complex.cos x - (1 - x ^ 2 / 2)))
      (c := Q - x ^ 2)]
  have eq : F / ((ξ - β₁) * (ξ - β₂)) + (L : ℂ) ^ 2 = (L : ℂ) ^ 2 * ((F + Q) / Q) := by
    rw [hPQ]; field_simp
  rw [eq, norm_mul, norm_pow, hnL, norm_div]
  have hQpos : 0 < ‖Q‖ := by linarith
  have : ‖F + Q‖ / ‖Q‖ ≤ 1 / 5 := by
    rw [div_le_iff₀ hQpos]; linarith
  have hL2 : 0 < L ^ 2 := by positivity
  calc L ^ 2 * (‖F + Q‖ / ‖Q‖) ≤ L ^ 2 * (1 / 5) := by gcongr
    _ = L ^ 2 / 5 := by ring

theorem differentiable_fn (κ : ℝ) (q : L2T L) (n : ℤ) : Differentiable ℂ (fn κ q n) := by
  intro w
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (QuantumNLS.LocalSpectral.pm L n : ℂ) + w) w :=
    (differentiableAt_const _).add differentiableAt_id
  have h2 := ((hD κ q) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)).comp w h1
  exact (h2.pow 2).sub_const 4

/-- eq. `GB01-factor` and eq. `GB01-H-bound` on the real slice. -/
theorem factor (hκ : 0 < κ) (q : L2T L) (n : ℤ)
    (ha : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fn κ q n w - freeF L w‖ ≤ 6 * ε₀)
    (hb : ∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 10 / 65536 ≤ ‖fn κ q n w‖)
    (hlm : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
          Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi))
    (hlp : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
          Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi)) :
    (∀ w : ℂ, ‖w‖ < 3 * dd L → fn κ q n w = Pn hκ q n w * Hn hκ q n w) ∧
    DifferentiableOn ℂ (Hn hκ q n) (ball 0 (3 * dd L)) ∧
    (∀ w : ℂ, ‖w‖ < 3 * dd L → ‖Hn hκ q n w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5) ∧
    (∀ w : ℂ, ‖w‖ ≤ 2 * dd L → ‖Hn hκ q n w + (L : ℂ) ^ 2‖ < L ^ 2 / 4) := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  obtain ⟨hsa, hsb, hzero, hmult⟩ := cell_count hκ q n hb hlm hlp
  set p := QuantumNLS.LocalSpectral.pm L n with hp_def
  set β₁ : ℂ := ((bm hκ q n - p : ℝ) : ℂ) with hβ₁
  set β₂ : ℂ := ((bp hκ q n - p : ℝ) : ℂ) with hβ₂
  have hn1 : ‖β₁‖ < dd L / 8 := by rw [hβ₁, Complex.norm_real, Real.norm_eq_abs]; exact hsa
  have hn2 : ‖β₂‖ < dd L / 8 := by rw [hβ₂, Complex.norm_real, Real.norm_eq_abs]; exact hsb
  have hF := differentiable_fn κ q n
  have hz1 : fn κ q n β₁ = 0 := (hzero β₁ (by linarith)).2 (Or.inl rfl)
  have hz2 : fn κ q n β₂ = 0 := (hzero β₂ (by linarith)).2 (Or.inr rfl)
  have hder : β₁ = β₂ → deriv (fn κ q n) β₁ = 0 := by
    intro heq
    rcases hmult with ⟨hlt, -, -⟩ | ⟨-, h2⟩
    · exfalso
      have h' := heq
      rw [hβ₁, hβ₂] at h'
      have : bm hκ q n - p = bp hκ q n - p := by exact_mod_cast h'
      linarith
    · have hd' : deriv (fn κ q n) β₁ = deriv (fun z => Dl κ q z ^ 2 - 4) ((p : ℂ) + β₁) :=
        deriv_comp_const_add (f := fun z => Dl κ q z ^ 2 - 4) (a := (p : ℂ)) (x := β₁)
      rw [hd']
      have hpt : (p : ℂ) + β₁ = (bm hκ q n : ℂ) := by rw [hβ₁]; push_cast; ring
      rw [hpt]
      exact deriv_zero_of_order_two ((((hD κ q).pow 2).sub_const 4).analyticAt _) h2
  obtain ⟨hG, hfac⟩ := dslope_factor hF hz1 hz2 hder
  set G := dslope (dslope (fn κ q n) β₁) β₂ with hG_def
  have hP : ∀ w, Pn hκ q n w = (w - β₁) * (w - β₂) := fun w => Pn_eq hκ q n w
  have hr : (3 * dd L) ≠ 0 := by positivity
  -- on the outer circle
  have hcirc : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L),
      Pn hκ q n ξ ≠ 0 ∧ fn κ q n ξ / Pn hκ q n ξ = G ξ ∧ ‖G ξ + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5 := by
    intro ξ hξ
    have hξn : ‖ξ‖ = 3 * dd L := by simpa using hξ
    obtain ⟨hP0, hbd⟩ := sphere_bound hξn hn1.le hn2.le (ha ξ (by rw [hξn]; linarith))
    rw [hP ξ]
    have hq : fn κ q n ξ / ((ξ - β₁) * (ξ - β₂)) = G ξ := by
      rw [hfac ξ]; exact mul_div_cancel_left₀ _ hP0
    refine ⟨hP0, hq, ?_⟩
    rw [← hq]; exact hbd
  have hHG : ∀ w ∈ ball (0 : ℂ) (3 * dd L), Hn hκ q n w = G w := by
    intro w hw
    unfold Hn
    have hcongr : (∮ ξ in C(0, 3 * dd L), (ξ - w)⁻¹ • (fn κ q n ξ / Pn hκ q n ξ)) =
        ∮ ξ in C(0, 3 * dd L), (ξ - w)⁻¹ • G ξ :=
      circleIntegral.integral_congr (by positivity) (fun ξ hξ => by
        rw [(hcirc ξ hξ).2.1])
    rw [hcongr, hG.differentiableOn.circleIntegral_sub_inv_smul hw, smul_eq_mul]
    have : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    field_simp
  have hbound : ∀ w : ℂ, ‖w‖ ≤ 3 * dd L → ‖G w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5 := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (3 * dd L))
      isBounded_ball (hG.add_const _).diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball (0 : ℂ) hr] at hz
      exact (hcirc z hz).2.2
    · rw [closure_ball (0 : ℂ) hr]; simpa using hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hHG w (by simpa using hw), hP w, hfac w]
  · exact hG.differentiableOn.congr (fun w hw => hHG w hw)
  · intro w hw
    rw [hHG w (by simpa using hw)]; exact hbound w hw.le
  · intro w hw
    have hw3 : ‖w‖ < 3 * dd L := by linarith
    rw [hHG w (by simpa using hw3)]
    have := hbound w hw3.le
    have hL2 : 0 < L ^ 2 := by positivity
    linarith

/-! ## The packaged count along the ray -/

/-- **Root count, symmetric functions and Cauchy quotient** (real slice; recorded route deviation, see module doc). -/
theorem root_count (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u : L2T L, ‖u - u₀‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) 1,
        (boundary hκ (t • u) (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
            Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi) ∧
        (boundary hκ (t • u) (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
            Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi) ∧
        bm hκ (t • u) n ≤ bp hκ (t • u) n ∧
        lev hκ (t • u) n = Icc (bm hκ (t • u) n) (bp hκ (t • u) n) ∧
        |bm hκ (t • u) n - QuantumNLS.LocalSpectral.pm L n| < dd L / 8 ∧
        |bp hκ (t • u) n - QuantumNLS.LocalSpectral.pm L n| < dd L / 8 ∧
        (∀ w : ℂ, ‖w‖ ≤ 4 * dd L → (fn κ (t • u) n w = 0 ↔
            w = ((bm hκ (t • u) n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ∨
            w = ((bp hκ (t • u) n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ))) ∧
        ((bm hκ (t • u) n < bp hκ (t • u) n ∧
            analyticOrderAt (fun z => Dl κ (t • u) z ^ 2 - 4) (bm hκ (t • u) n : ℂ) = 1 ∧
            analyticOrderAt (fun z => Dl κ (t • u) z ^ 2 - 4) (bp hκ (t • u) n : ℂ) = 1) ∨
          (bm hκ (t • u) n = bp hκ (t • u) n ∧
            analyticOrderAt (fun z => Dl κ (t • u) z ^ 2 - 4) (bm hκ (t • u) n : ℂ) = 2)) ∧
        (∀ w : ℂ, ‖w‖ < 3 * dd L → fn κ (t • u) n w = Pn hκ (t • u) n w * Hn hκ (t • u) n w) ∧
        DifferentiableOn ℂ (Hn hκ (t • u) n) (ball 0 (3 * dd L)) ∧
        (∀ w : ℂ, ‖w‖ ≤ 2 * dd L → ‖Hn hκ (t • u) n w + (L : ℂ) ^ 2‖ < L ^ 2 / 4) := by
  obtain ⟨N, ρ, hρ, h⟩ := root_prep κ u₀
  refine ⟨N, ρ, hρ, fun n hn u hu t ht => ?_⟩
  have ep : ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((dd L : ℝ) : ℂ)) =
      ((QuantumNLS.LocalSpectral.pm L n + dd L : ℝ) : ℂ) := by push_cast; ring
  have em : ((QuantumNLS.LocalSpectral.pm L n : ℂ) + ((-dd L : ℝ) : ℂ)) =
      ((QuantumNLS.LocalSpectral.pm L n - dd L : ℝ) : ℂ) := by push_cast; ring
  have hm : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (s • u) ((QuantumNLS.LocalSpectral.pm L n - dd L : ℝ) : ℂ)‖ < 2 := by
    intro s hs; have := (h n hn u hu s hs).2.2.2.2.1; rw [em] at this; exact this
  have hp : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖Dl κ (s • u) ((QuantumNLS.LocalSpectral.pm L n + dd L : ℝ) : ℂ)‖ < 2 := by
    intro s hs; have := (h n hn u hu s hs).2.2.2.1; rw [ep] at this; exact this
  obtain ⟨hlm, hlp⟩ := labels hκ u n hm hp t ht
  obtain ⟨ha, hb, -, -, -, -⟩ := h n hn u hu t ht
  obtain ⟨hle, hS⟩ := lev_eq hκ (t • u) n
  obtain ⟨hsa, hsb, hzero, hmult⟩ := cell_count hκ (t • u) n hb hlm hlp
  obtain ⟨hfac, hdiff, -, hH⟩ := factor hκ (t • u) n ha hb hlm hlp
  exact ⟨hlm, hlp, hle, hS, hsa, hsb, hzero, hmult, hfac, hdiff, hH⟩

end QuantumNLS.RB01RootCount

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01RootCount.lev_eq
#print axioms QuantumNLS.RB01RootCount.labels
#print axioms QuantumNLS.RB01RootCount.cell_count
#print axioms QuantumNLS.RB01RootCount.sphere_bound
#print axioms QuantumNLS.RB01RootCount.factor
#print axioms QuantumNLS.RB01RootCount.root_count
