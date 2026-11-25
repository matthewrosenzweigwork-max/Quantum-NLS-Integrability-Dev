import Mathlib
import QuantumNLS.RootGapMultiplicity

/-!
# R-0908DFDE `prop:root-gap-multiplicity`: the level sets of the boundary phase and the endpoint dichotomy

Continues `RootGapMultiplicity` (parts (A), (B)): parts (C), (D) of the statement, see there.  Everything is for the actual quantum measure and the actual
`Δ = L2SpatialTransfer.discriminant κ u`, `θ = Re (boundary hκ u)`.

Route (the printed one, with one simplification): on the level set `S_n = {θ = nπ}` one has `Re Δ = 2 σ_n cosh (Im b)`, hence `|Re Δ| ≥ 2` on `S_n`
(`two_le_abs`); so a band point (`|Δ| < 2`) is never in `S_n`.  An interior point of `S_n` with `|Δ| = 2` would be a real zero (order 1 or 2) with band points arbitrarily
close, contradicting `S_n`-membership of a neighborhood; endpoints are zeros whose order is read off from the sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootGapLevelSets

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.PhysicalContinuousBoundary (boundary continuous_boundary boundary_limit boundary_cosine boundary_im
  gap_constancy monotone_all onto_all boundary_zero)
open QuantumNLS.RootGapLocal
open QuantumNLS.RootGapMultiplicity
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg)
open QuantumNLS.RootDensity (hfun hfun_pos_iff hfun_nonneg)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The level set `S_n = {θ = nπ}`. -/
def lev (hκ : 0 < κ) (u : L2T L) (n : ℤ) : Set ℝ := {x | (boundary hκ u x).re = (n : ℝ) * Real.pi}

theorem continuous_re_boundary (hκ : 0 < κ) (u : L2T L) : Continuous fun x => (boundary hκ u x).re :=
  Complex.continuous_re.comp (continuous_boundary hκ u)

theorem continuous_re_Delta (κ : ℝ) (u : L2T L) : Continuous fun x : ℝ => (Dl κ u (x : ℂ)).re :=
  Complex.continuous_re.comp ((hD κ u).continuous.comp Complex.continuous_ofReal)

theorem int_eq_of_sandwich {n k : ℤ} (h1 : (n : ℝ) - 1 / 2 ≤ k) (h2 : (k : ℝ) ≤ n + 1 / 2) : k = n := by
  have a : ((n - 1 : ℤ) : ℝ) < k := by push_cast; linarith
  have b : (k : ℝ) < ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  have a' := Int.cast_lt.1 a
  have b' := Int.cast_lt.1 b
  omega

theorem dens_pos_iff (hκ : 0 < κ) (u : L2T L) (t : ℝ) : 0 < dens κ u t ↔ 2 < |(Dl κ u (t : ℂ)).re| := by
  unfold dens
  rw [mul_pos_iff_of_pos_left (by positivity : 0 < (Real.pi * κ)⁻¹)]
  exact hfun_pos_iff _

/-! ### On a level set: `|Re Δ| ≥ 2` -/

theorem re_Delta_of_level (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ} (hx : x ∈ lev hκ u n) :
    (Dl κ u (x : ℂ)).re = 2 * sgn n * Real.cosh (boundary hκ u x).im := by
  have h := congrArg Complex.re (boundary_cosine hκ u x)
  have h2 : (2 * Complex.cos (boundary hκ u x)).re =
      2 * (Real.cos (boundary hκ u x).re * Real.cosh (boundary hκ u x).im) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, re_cos]
  rw [← h, h2]
  have hx' : (boundary hκ u x).re = (n : ℝ) * Real.pi := hx
  rw [hx', Real.cos_int_mul_pi]
  simp only [sgn]; ring

theorem two_le_sgn_mul (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ} (hx : x ∈ lev hκ u n) :
    2 ≤ sgn n * (Dl κ u (x : ℂ)).re := by
  rw [re_Delta_of_level hκ u hx]
  have e : sgn n * (2 * sgn n * Real.cosh (boundary hκ u x).im) = 2 * Real.cosh (boundary hκ u x).im := by
    have := sgn_sq n
    calc sgn n * (2 * sgn n * Real.cosh (boundary hκ u x).im) =
        2 * sgn n ^ 2 * Real.cosh (boundary hκ u x).im := by ring
      _ = _ := by rw [this]; ring
  rw [e]
  linarith [Real.one_le_cosh (boundary hκ u x).im]

theorem two_le_abs (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ} (hx : x ∈ lev hκ u n) :
    2 ≤ |(Dl κ u (x : ℂ)).re| := by
  have h := two_le_sgn_mul hκ u hx
  rcases sgn_cases n with e | e
  · rw [e] at h; exact le_trans (by linarith) (le_abs_self _)
  · rw [e] at h; exact le_trans (by linarith) (neg_le_abs _)

theorem im_boundary_eq_zero (hκ : 0 < κ) (u : L2T L) {x : ℝ} (h : |(Dl κ u (x : ℂ)).re| ≤ 2) :
    (boundary hκ u x).im = 0 := by
  rw [boundary_im]
  by_contra hne
  have : 0 < hfun |(Dl κ u (x : ℂ)).re| := lt_of_le_of_ne (hfun_nonneg _) (Ne.symm hne)
  exact absurd ((hfun_pos_iff _).1 this) (not_lt.2 h)

theorem boundary_eq_of_level (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ} (hx : x ∈ lev hκ u n)
    (h : |(Dl κ u (x : ℂ)).re| ≤ 2) : boundary hκ u x = (n : ℂ) * Real.pi := by
  have hx' : (boundary hκ u x).re = (n : ℝ) * Real.pi := hx
  refine Complex.ext (by rw [hx']; simp) (by rw [im_boundary_eq_zero hκ u h]; simp)

/-! ### Neighborhoods -/

theorem level_nbhd (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ} (hx : x ∈ lev hκ u n)
    (hg : 2 < |(Dl κ u (x : ℂ)).re|) : ∃ l r : ℝ, l < x ∧ x < r ∧ Ioo l r ⊆ lev hκ u n := by
  have hU : IsOpen {y : ℝ | 2 < |(Dl κ u (y : ℂ)).re|} :=
    isOpen_lt continuous_const (continuous_re_Delta κ u).abs
  obtain ⟨l, r, hxlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hU.mem_nhds hg)
  obtain ⟨k, hk⟩ := gap_constancy hκ u (hxlr.1.trans hxlr.2) (fun y hy => hsub hy)
  have hkn : k = n := by
    have h1 := hk x hxlr
    have h2 : (boundary hκ u x).re = (n : ℝ) * Real.pi := hx
    have : (k : ℝ) * Real.pi = n * Real.pi := h1.symm.trans h2
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero this
  refine ⟨l, r, hxlr.1, hxlr.2, fun y hy => ?_⟩
  have := hk y hy
  rw [hkn] at this
  exact this

theorem gap_side_right (hκ : 0 < κ) (u : L2T L) {b r : ℝ} {n : ℤ} (hb : b ∈ lev hκ u n) (hlt : b < r)
    (hU : ∀ y ∈ Ioo b r, 2 < |(Dl κ u (y : ℂ)).re|) : Ioo b r ⊆ lev hκ u n := by
  obtain ⟨k, hk⟩ := gap_constancy hκ u hlt hU
  have h1 : Tendsto (fun x => (boundary hκ u x).re) (𝓝[>] b) (𝓝 ((boundary hκ u b).re)) :=
    ((continuous_re_boundary hκ u).tendsto b).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x => (boundary hκ u x).re) (𝓝[>] b) (𝓝 ((k : ℝ) * Real.pi)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hlt] with y hy using (hk y hy).symm)
  have h3 := tendsto_nhds_unique h1 h2
  have hkn : k = n := by
    have h2' : (boundary hκ u b).re = (n : ℝ) * Real.pi := hb
    have : (k : ℝ) * Real.pi = n * Real.pi := h3.symm.trans h2'
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero this
  intro y hy
  have := hk y hy
  rw [hkn] at this
  exact this

theorem gap_side_left (hκ : 0 < κ) (u : L2T L) {b l : ℝ} {n : ℤ} (hb : b ∈ lev hκ u n) (hlt : l < b)
    (hU : ∀ y ∈ Ioo l b, 2 < |(Dl κ u (y : ℂ)).re|) : Ioo l b ⊆ lev hκ u n := by
  obtain ⟨k, hk⟩ := gap_constancy hκ u hlt hU
  have h1 : Tendsto (fun x => (boundary hκ u x).re) (𝓝[<] b) (𝓝 ((boundary hκ u b).re)) :=
    ((continuous_re_boundary hκ u).tendsto b).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x => (boundary hκ u x).re) (𝓝[<] b) (𝓝 ((k : ℝ) * Real.pi)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsLT hlt] with y hy using (hk y hy).symm)
  have h3 := tendsto_nhds_unique h1 h2
  have hkn : k = n := by
    have h2' : (boundary hκ u b).re = (n : ℝ) * Real.pi := hb
    have : (k : ℝ) * Real.pi = n * Real.pi := h3.symm.trans h2'
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero this
  intro y hy
  have := hk y hy
  rw [hkn] at this
  exact this

/-! ### The level set is a closed bounded interval -/

theorem exists_separator (hκ : 0 < κ) (u : L2T L) (r : ℝ) : ∃ a : ℝ, (boundary hκ u a).re = r :=
  onto_all hκ u r

theorem level_between (hκ : 0 < κ) (u : L2T L) (n : ℤ) {a a' : ℝ}
    (ha : (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi)
    (ha' : (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi) {x : ℝ} (hx : x ∈ lev hκ u n) :
    a < x ∧ x < a' := by
  have hmono := monotone_all hκ u
  have hx' : (boundary hκ u x).re = (n : ℝ) * Real.pi := hx
  have hpi := Real.pi_pos
  constructor
  · by_contra h
    push Not at h
    have := hmono h
    simp only at this
    rw [hx', ha] at this
    nlinarith
  · by_contra h
    push Not at h
    have := hmono h
    simp only at this
    rw [hx', ha'] at this
    nlinarith

theorem level_interval (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∃ bm bp : ℝ, bm ≤ bp ∧ lev hκ u n = Icc bm bp := by
  have hmono := monotone_all hκ u
  obtain ⟨x0, hx0⟩ := onto_all hκ u ((n : ℝ) * Real.pi)
  obtain ⟨a, ha⟩ := onto_all hκ u (((n : ℝ) - 1 / 2) * Real.pi)
  obtain ⟨a', ha'⟩ := onto_all hκ u (((n : ℝ) + 1 / 2) * Real.pi)
  simp only at hx0 ha ha'
  set S := lev hκ u n with hSdef
  have hne : S.Nonempty := ⟨x0, hx0⟩
  have hbtw : ∀ x ∈ S, a < x ∧ x < a' := fun x hx => level_between hκ u n ha ha' hx
  have hbl : BddBelow S := ⟨a, fun x hx => (hbtw x hx).1.le⟩
  have hbu : BddAbove S := ⟨a', fun x hx => (hbtw x hx).2.le⟩
  have hcl : IsClosed S := isClosed_eq (continuous_re_boundary hκ u) continuous_const
  have hoc : S.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    have h1 : (boundary hκ u x).re = (n : ℝ) * Real.pi := hx
    have h2 : (boundary hκ u y).re = (n : ℝ) * Real.pi := hy
    have a1 := hmono hz.1
    have a2 := hmono hz.2
    simp only at a1 a2
    show (boundary hκ u z).re = (n : ℝ) * Real.pi
    linarith
  have hbm : sInf S ∈ S := hcl.csInf_mem hne hbl
  have hbp : sSup S ∈ S := hcl.csSup_mem hne hbu
  refine ⟨sInf S, sSup S, csInf_le_csSup hne hbl hbu, ?_⟩
  ext z
  constructor
  · intro hz; exact ⟨csInf_le hbl hz, le_csSup hbu hz⟩
  · intro hz; exact hoc.out hbm hbp hz

/-! ### Zeros: band points arbitrarily close -/

theorem frequently_band (hκ : 0 < κ) (u : L2T L) {x : ℝ} {n : ℤ}
    (hn : boundary hκ u x = (n : ℂ) * Real.pi) :
    ∃ᶠ t : ℝ in 𝓝[≠] x, |(Dl κ u (t : ℂ)).re| < 2 := by
  obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u x n hn
  rcases order_cases' hκ u x n hn with h1 | h2
  · rcases simple_sides (hD κ u) (hreal κ u) (sgn_cases n) hDx h1 with ⟨-, hb⟩ | ⟨-, hb⟩
    · exact hb.frequently.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_lt ht))
    · exact hb.frequently.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  · exact (double_strict (hD κ u) (hreal κ u) (sgn_cases n) Fact.out hray hDx h2).frequently

/-! ### The dichotomy -/

theorem level_dichotomy (hκ : 0 < κ) (u : L2T L) (n : ℤ) {bm bp : ℝ} (hle : bm ≤ bp)
    (hS : lev hκ u n = Icc bm bp) :
    |(Dl κ u (bm : ℂ)).re| ≤ 2 ∧ |(Dl κ u (bp : ℂ)).re| ≤ 2 ∧
    ((bm < bp ∧ (∀ x ∈ Ioo bm bp, 2 < |(Dl κ u (x : ℂ)).re|) ∧
        analyticOrderAt (fun z => Dl κ u z - 2 * (sgn n : ℂ)) (bm : ℂ) = 1 ∧
        analyticOrderAt (fun z => Dl κ u z - 2 * (sgn n : ℂ)) (bp : ℂ) = 1) ∨
     (bm = bp ∧ analyticOrderAt (fun z => Dl κ u z - 2 * (sgn n : ℂ)) (bm : ℂ) = 2)) := by
  have hbmS : bm ∈ lev hκ u n := by rw [hS]; exact left_mem_Icc.2 hle
  have hbpS : bp ∈ lev hκ u n := by rw [hS]; exact right_mem_Icc.2 hle
  have hbp_le : |(Dl κ u (bp : ℂ)).re| ≤ 2 := by
    by_contra h
    push Not at h
    obtain ⟨l, r, hl, hr, hsub⟩ := level_nbhd hκ u hbpS h
    have hmid : (bp + r) / 2 ∈ lev hκ u n := hsub ⟨by linarith, by linarith⟩
    rw [hS] at hmid
    linarith [hmid.2]
  have hbm_le : |(Dl κ u (bm : ℂ)).re| ≤ 2 := by
    by_contra h
    push Not at h
    obtain ⟨l, r, hl, hr, hsub⟩ := level_nbhd hκ u hbmS h
    have hmid : (l + bm) / 2 ∈ lev hκ u n := hsub ⟨by linarith, by linarith⟩
    rw [hS] at hmid
    linarith [hmid.1]
  have hbpb := boundary_eq_of_level hκ u hbpS hbp_le
  have hbmb := boundary_eq_of_level hκ u hbmS hbm_le
  refine ⟨hbm_le, hbp_le, ?_⟩
  by_cases hlt : bm < bp
  · left
    have hint : ∀ x ∈ Ioo bm bp, 2 < |(Dl κ u (x : ℂ)).re| := by
      intro x hx
      by_contra hnot
      push Not at hnot
      have hxS : x ∈ lev hκ u n := by rw [hS]; exact ⟨hx.1.le, hx.2.le⟩
      have hxb := boundary_eq_of_level hκ u hxS hnot
      have hfreq := frequently_band hκ u hxb
      have hev : ∀ᶠ t : ℝ in 𝓝[≠] x, t ∈ Ioo bm bp :=
        nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)
      obtain ⟨t, ht1, ht2⟩ := (hfreq.and_eventually hev).exists
      have htS : t ∈ lev hκ u n := by rw [hS]; exact ⟨ht2.1.le, ht2.2.le⟩
      linarith [two_le_abs hκ u htS]
    refine ⟨hlt, hint, ?_, ?_⟩
    · rcases order_cases' hκ u bm n hbmb with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u bm n hbmb
        have hd := double_strict (hD κ u) (hreal κ u) (sgn_cases n) Fact.out hray hDx h2
        have hd' := hd.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_gt ht : Ioi bm ⊆ {bm}ᶜ))
        have hev : ∀ᶠ t : ℝ in 𝓝[>] bm, t ∈ Ioo bm bp := Ioo_mem_nhdsGT hlt
        obtain ⟨t, ht1, ht2⟩ := (hd'.and hev).exists
        have htS : t ∈ lev hκ u n := by rw [hS]; exact ⟨ht2.1.le, ht2.2.le⟩
        linarith [two_le_abs hκ u htS]
    · rcases order_cases' hκ u bp n hbpb with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u bp n hbpb
        have hd := double_strict (hD κ u) (hreal κ u) (sgn_cases n) Fact.out hray hDx h2
        have hd' := hd.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_lt ht : Iio bp ⊆ {bp}ᶜ))
        have hev : ∀ᶠ t : ℝ in 𝓝[<] bp, t ∈ Ioo bm bp := Ioo_mem_nhdsLT hlt
        obtain ⟨t, ht1, ht2⟩ := (hd'.and hev).exists
        have htS : t ∈ lev hκ u n := by rw [hS]; exact ⟨ht2.1.le, ht2.2.le⟩
        linarith [two_le_abs hκ u htS]
  · right
    have heq : bm = bp := le_antisymm hle (not_lt.1 hlt)
    refine ⟨heq, ?_⟩
    rcases order_cases' hκ u bm n hbmb with h1 | h2
    · exfalso
      obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u bm n hbmb
      rcases simple_sides (hD κ u) (hreal κ u) (sgn_cases n) hDx h1 with ⟨hgap, -⟩ | ⟨hgap, -⟩
      · obtain ⟨r, hr, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hgap
        have hs := gap_side_right hκ u hbmS hr (fun y hy => hsub hy)
        have hmid : (bm + r) / 2 ∈ lev hκ u n := hs ⟨by linarith [hr.out], by linarith [hr.out]⟩
        rw [hS, ← heq] at hmid
        linarith [hmid.2, hr.out]
      · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hgap
        have hs := gap_side_left hκ u hbmS hl (fun y hy => hsub hy)
        have hmid : (l + bm) / 2 ∈ lev hκ u n := hs ⟨by linarith [hl.out], by linarith [hl.out]⟩
        rw [hS, ← heq] at hmid
        linarith [hmid.1, hl.out]
    · exact h2

/-! ### Masses -/

theorem measure_eq_dens (hκ : 0 < κ) (u : L2T L) :
    measure hκ u = volume.withDensity (fun t => ENNReal.ofReal (dens κ u t)) := by
  by_cases hu : u = 0
  · subst hu
    have h0 : ∀ t, dens κ (0 : L2T L) t = 0 := by
      intro t
      have hi := boundary_im hκ (0 : L2T L) t
      rw [boundary_zero hκ t] at hi
      have : hfun |(Dl κ (0 : L2T L) (t : ℂ)).re| = 0 := by
        rw [← hi]; simp
      unfold dens
      rw [this, mul_zero]
    rw [QuantumNLS.PhysicalQuantumMeasure.measure_zero]
    simp [h0]
  · exact QuantumNLS.RootDensityIdentification.root_density hκ hu

theorem measure_pos_of (hκ : 0 < κ) (u : L2T L) {c d : ℝ} (hcd : c < d)
    (hpos : ∀ x ∈ Ioo c d, 0 < dens κ u x) : 0 < measure hκ u (Ioo c d) := by
  rw [measure_eq_dens hκ u, withDensity_apply _ measurableSet_Ioo]
  by_contra h
  push Not at h
  have h0 : ∫⁻ x in Ioo c d, ENNReal.ofReal (dens κ u x) = 0 := le_antisymm h bot_le
  have hm : Measurable fun x => ENNReal.ofReal (dens κ u x) :=
    ENNReal.measurable_ofReal.comp (continuous_dens κ u).measurable
  rw [lintegral_eq_zero_iff hm, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at h0
  have hnull : volume (Ioo c d) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h0] with x hx hxm
    have := hx hxm
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact absurd (hpos x hxm) (not_lt.2 this)
  rw [Real.volume_Ioo] at hnull
  simp at hnull
  linarith

theorem measure_zero_cell (hκ : 0 < κ) (u : L2T L) (n : ℤ) {b a a' : ℝ} (hS : lev hκ u n = Icc b b)
    (hb : |(Dl κ u (b : ℂ)).re| ≤ 2)
    (ha : (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi)
    (ha' : (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi) : measure hκ u (Ioo a a') = 0 := by
  rw [measure_eq_dens hκ u, withDensity_apply _ measurableSet_Ioo]
  have hmono := monotone_all hκ u
  have hpi := Real.pi_pos
  have hz : ∀ x ∈ Ioo a a', dens κ u x = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < dens κ u x := lt_of_le_of_ne (dens_nonneg hκ u x) (Ne.symm hne)
    have hg := (dens_pos_iff hκ u x).1 hpos
    have hU : IsOpen {y : ℝ | 2 < |(Dl κ u (y : ℂ)).re|} :=
      isOpen_lt continuous_const (continuous_re_Delta κ u).abs
    obtain ⟨l, r, hxlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hU.mem_nhds hg)
    obtain ⟨k, hk⟩ := gap_constancy hκ u (hxlr.1.trans hxlr.2) (fun y hy => hsub hy)
    have hxk := hk x hxlr
    have s1 := hmono hx.1.le
    have s2 := hmono hx.2.le
    simp only at s1 s2
    rw [ha, hxk] at s1
    rw [ha', hxk] at s2
    have hkn : k = n := by
      apply int_eq_of_sandwich
      · by_contra hh; push Not at hh; nlinarith
      · by_contra hh; push Not at hh; nlinarith
    have hxS : x ∈ lev hκ u n := by
      show (boundary hκ u x).re = (n : ℝ) * Real.pi
      rw [hxk, hkn]
    rw [hS] at hxS
    have hxb : x = b := le_antisymm hxS.2 hxS.1
    rw [hxb] at hg
    linarith
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 0) (fun x hx => by simp [hz x hx])]
  simp

/-! ### The proposition -/

theorem root_gap_multiplicity (hκ : 0 < κ) (u : L2T L) :
    (∀ z : ℂ, Dl κ u z ^ 2 - 4 = 0 → z.im = 0 ∧ analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) z ≤ 2) ∧
    (∀ x : ℝ, analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) (x : ℂ) = 2 →
      (∀ᶠ t : ℝ in 𝓝[<] x, |(Dl κ u (t : ℂ)).re| < 2) ∧ (∀ᶠ t : ℝ in 𝓝[>] x, |(Dl κ u (t : ℂ)).re| < 2)) ∧
    (∀ n : ℤ, ∃ a : ℝ, (boundary hκ u a).re = ((n : ℝ) + 1 / 2) * Real.pi) ∧
    (∀ n : ℤ, ∃ bm bp : ℝ, bm ≤ bp ∧ {x : ℝ | (boundary hκ u x).re = (n : ℝ) * Real.pi} = Icc bm bp ∧
      (∀ a a' : ℝ, (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi →
        (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi →
        a < bm ∧ bp < a' ∧ (0 < measure hκ u (Ioo a a') ↔ bm < bp)) ∧
      ((bm < bp ∧ (∀ x ∈ Ioo bm bp, 0 < dens κ u x) ∧
          analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bm : ℂ) = 1 ∧
          analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bp : ℂ) = 1) ∨
       (bm = bp ∧ analyticOrderAt (fun z => Dl κ u z - 2 * (((-1 : ℝ) ^ n : ℝ) : ℂ)) (bm : ℂ) = 2 ∧
          ∀ a a' : ℝ, (boundary hκ u a).re = ((n : ℝ) - 1 / 2) * Real.pi →
            (boundary hκ u a').re = ((n : ℝ) + 1 / 2) * Real.pi → measure hκ u (Ioo a a') = 0))) := by
  obtain ⟨hA, hB⟩ := zeros_and_double hκ u
  refine ⟨hA, hB, fun n => exists_separator hκ u _, fun n => ?_⟩
  obtain ⟨bm, bp, hle, hS⟩ := level_interval hκ u n
  obtain ⟨hbm, hbp, hdich⟩ := level_dichotomy hκ u n hle hS
  have hsgn : ((-1 : ℝ) ^ n : ℝ) = sgn n := rfl
  simp only [hsgn]
  refine ⟨bm, bp, hle, hS, ?_, ?_⟩
  · intro a a' ha ha'
    have hbmS : bm ∈ lev hκ u n := by rw [hS]; exact left_mem_Icc.2 hle
    have hbpS : bp ∈ lev hκ u n := by rw [hS]; exact right_mem_Icc.2 hle
    obtain ⟨h1, -⟩ := level_between hκ u n ha ha' hbmS
    obtain ⟨-, h2⟩ := level_between hκ u n ha ha' hbpS
    refine ⟨h1, h2, ?_⟩
    rcases hdich with ⟨hlt, hint, -, -⟩ | ⟨heq, -⟩
    · constructor
      · intro _; exact hlt
      · intro _
        have hpos : 0 < measure hκ u (Ioo bm bp) :=
          measure_pos_of hκ u hlt (fun x hx => (dens_pos_iff hκ u x).2 (hint x hx))
        exact lt_of_lt_of_le hpos (measure_mono (Ioo_subset_Ioo h1.le h2.le))
    · constructor
      · intro hpos
        by_contra hnot
        have heq' : lev hκ u n = Icc bm bm := by rw [hS, ← heq]
        have := measure_zero_cell hκ u n (b := bm) (by rw [hS, ← heq]) hbm ha ha'
        rw [this] at hpos
        exact lt_irrefl _ hpos
      · intro h; exact absurd h (not_lt.2 heq.ge)
  · rcases hdich with ⟨hlt, hint, o1, o2⟩ | ⟨heq, o⟩
    · left
      exact ⟨hlt, fun x hx => (dens_pos_iff hκ u x).2 (hint x hx), o1, o2⟩
    · right
      refine ⟨heq, o, fun a a' ha ha' => ?_⟩
      exact measure_zero_cell hκ u n (b := bm) (by rw [hS, ← heq]) hbm ha ha'

end QuantumNLS.RootGapLevelSets

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootGapLevelSets.level_dichotomy
#print axioms QuantumNLS.RootGapLevelSets.root_gap_multiplicity
