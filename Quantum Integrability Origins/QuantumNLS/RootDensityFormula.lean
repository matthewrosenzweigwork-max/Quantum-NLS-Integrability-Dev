import Mathlib

/-!
# R-7E0532E7 `thm:root-spectral-density`: the real-analysis content (density formula, bound, components, endpoints)

(`source/chapters/foundations/ROOT_spectral_density.tex`; the statement part after `eq:root-explicit-density`.)

PURE real analysis, independent of DEF-013/EXT-025/R-09E1EAE9: for a real function `Δ` on `ℝ` (the discriminant
`t ↦ Δ_u(t)`, real on the real axis) with the properties

* (H1) continuity,
* (H2) the real trace bound `|Δ(t)| ≤ 2 cosh(√κ ‖u‖₁)`,
* (H3) `|Δ| ≤ 2` at points tending to `±∞` (the source: `Δ(t) - 2cos(tL/2) → 0` and `cos = 0` at `(2j+1)π/L`),
* (H4) `Δ` is the restriction of an entire function and `|Δ| ≢ 2` (nonconstant `Δ² - 4`),

we prove, literally as in the statement:

* `rootDensity κ Δ t = (πκ)⁻¹ · (arcosh(|Δ t|/2) if |Δ t| > 2 else 0)` is continuous (`continuous_rootDensity`),
  nonnegative, positive exactly on `{|Δ| > 2}` (`rootDensity_pos_iff`), and bounded by `‖u‖₁/(π√κ)` (`rootDensity_le`);
* every connected component of `{|Δ| > 2}` is a bounded open interval `(a,b)` with `|Δ a| = |Δ b| = 2`
  (`connectedComponentIn_eq_Ioo`);
* `{|Δ| = 2}`, hence the set of all endpoints, is finite on every compact interval (`finite_endpoints`);
* the measure with this continuous density has support the closure of `{|Δ| > 2}` (`support_withDensity`).

What this module does NOT do (named in the checkpoint): it does not identify the root measure `μ_{κ,u}` of
`thm:root-measure` (R-09E1EAE9) with `volume.withDensity rootDensity` (the Poisson-boundary-value argument uses the
quantum identity `2 cos γ = Δ`, DEF-010 Cauchy transform, EXT-025 instances), and takes H1-H4 as hypotheses about `Δ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace QuantumNLS.RootDensity

/-- `h(r) = arcosh(r/2)` for `r > 2` and `0` for `r ≤ 2`. -/
def hfun (r : ℝ) : ℝ := if 2 < r then Real.arcosh (r / 2) else 0

theorem hfun_eq_arcosh_max (r : ℝ) : hfun r = Real.arcosh (max (r / 2) 1) := by
  unfold hfun
  by_cases h : 2 < r
  · rw [if_pos h, max_eq_left (by linarith)]
  · rw [if_neg h, max_eq_right (by linarith [not_lt.mp h]), Real.arcosh_zero]

theorem continuous_hfun : Continuous hfun := by
  have : hfun = fun r => Real.arcosh (max (r / 2) 1) := funext hfun_eq_arcosh_max
  rw [this]
  exact Real.continuousOn_arcosh.comp_continuous (by fun_prop) (fun r => mem_Ici.2 (le_max_right _ _))

theorem hfun_nonneg (r : ℝ) : 0 ≤ hfun r := by
  rw [hfun_eq_arcosh_max]
  exact Real.arcosh_nonneg (le_max_right _ _)

theorem hfun_pos_iff (r : ℝ) : 0 < hfun r ↔ 2 < r := by
  unfold hfun
  constructor
  · intro h
    by_contra hr
    rw [if_neg hr] at h
    exact lt_irrefl _ h
  · intro h
    rw [if_pos h]
    exact Real.arcosh_pos (by linarith)

/-- The density `(πκ)⁻¹ · h(|Δ(t)|)` of `eq:root-explicit-density`. -/
def rootDensity (κ : ℝ) (Δ : ℝ → ℝ) (t : ℝ) : ℝ := (Real.pi * κ)⁻¹ * hfun |Δ t|

theorem continuous_rootDensity {κ : ℝ} {Δ : ℝ → ℝ} (hΔ : Continuous Δ) :
    Continuous (rootDensity κ Δ) :=
  continuous_const.mul (continuous_hfun.comp hΔ.abs)

theorem rootDensity_nonneg {κ : ℝ} (hκ : 0 < κ) (Δ : ℝ → ℝ) (t : ℝ) : 0 ≤ rootDensity κ Δ t :=
  mul_nonneg (inv_nonneg.2 (mul_nonneg Real.pi_pos.le hκ.le)) (hfun_nonneg _)

theorem rootDensity_pos_iff {κ : ℝ} (hκ : 0 < κ) (Δ : ℝ → ℝ) (t : ℝ) :
    0 < rootDensity κ Δ t ↔ 2 < |Δ t| := by
  unfold rootDensity
  rw [← hfun_pos_iff]
  exact mul_pos_iff_of_pos_left (inv_pos.2 (mul_pos Real.pi_pos hκ))

theorem rootDensity_eq_zero_iff {κ : ℝ} (hκ : 0 < κ) (Δ : ℝ → ℝ) (t : ℝ) :
    rootDensity κ Δ t = 0 ↔ |Δ t| ≤ 2 := by
  have h1 := rootDensity_nonneg hκ Δ t
  have h2 := rootDensity_pos_iff hκ Δ t
  constructor
  · intro h
    by_contra hc
    have := h2.2 (not_le.mp hc)
    linarith
  · intro h
    by_contra hc
    exact absurd (h2.1 (lt_of_le_of_ne h1 (Ne.symm hc))) (not_lt.2 h)

/-- **`eq:root-density-Linfty`**: under the real trace bound `|Δ| ≤ 2cosh(√κ c)` (`c = ‖u‖₁`),
`0 ≤ density ≤ c/(π√κ)`. -/
theorem rootDensity_le {κ : ℝ} (hκ : 0 < κ) {Δ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΔ : ∀ t, |Δ t| ≤ 2 * Real.cosh (Real.sqrt κ * c)) (t : ℝ) :
    rootDensity κ Δ t ≤ c / (Real.pi * Real.sqrt κ) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hh : hfun |Δ t| ≤ Real.sqrt κ * c := by
    unfold hfun
    split_ifs with h
    · have h1 : |Δ t| / 2 ≤ Real.cosh (Real.sqrt κ * c) := by linarith [hΔ t]
      have h2 := (Real.arcosh_le_arcosh (by linarith) (Real.cosh_pos _)).2 h1
      rwa [Real.arcosh_cosh (by positivity)] at h2
    · positivity
  unfold rootDensity
  calc (Real.pi * κ)⁻¹ * hfun |Δ t| ≤ (Real.pi * κ)⁻¹ * (Real.sqrt κ * c) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
    _ = c / (Real.pi * Real.sqrt κ) := by
        have hsq := Real.mul_self_sqrt hκ.le
        rw [inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (Real.pi * c) * hsq

/-! ### Components of `{|Δ| > 2}` -/

/-- Every connected component of the open set `{|Δ| > 2}` is a bounded open interval `(a,b)`, with `|Δ a| = |Δ b| = 2`,
provided `|Δ| ≤ 2` at points going to `+∞` and to `-∞`. -/
theorem connectedComponentIn_eq_Ioo {Δ : ℝ → ℝ} (hΔ : Continuous Δ)
    (hpos : ∀ R : ℝ, ∃ p, R ≤ p ∧ |Δ p| ≤ 2) (hneg : ∀ R : ℝ, ∃ p, p ≤ R ∧ |Δ p| ≤ 2)
    {x : ℝ} (hx : 2 < |Δ x|) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ connectedComponentIn {t | 2 < |Δ t|} x = Ioo a b ∧
      |Δ a| = 2 ∧ |Δ b| = 2 := by
  set U : Set ℝ := {t | 2 < |Δ t|} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const hΔ.abs
  have hxU : x ∈ U := hx
  -- right endpoint
  set Sp : Set ℝ := {p | x ≤ p ∧ |Δ p| ≤ 2} with hSp
  have hSpc : IsClosed Sp := (isClosed_Ici).inter (isClosed_le hΔ.abs continuous_const)
  obtain ⟨p0, hp0, hp0'⟩ := hpos x
  have hSpne : Sp.Nonempty := ⟨p0, hp0, hp0'⟩
  have hSpb : BddBelow Sp := ⟨x, fun p hp => hp.1⟩
  set b := sInf Sp with hb
  have hbS : b ∈ Sp := hSpc.csInf_mem hSpne hSpb
  have hxb : x < b := lt_of_le_of_ne hbS.1 (fun h => by
    have := hbS.2; rw [← h] at this; linarith)
  -- left endpoint
  set Sn : Set ℝ := {p | p ≤ x ∧ |Δ p| ≤ 2} with hSn
  have hSnc : IsClosed Sn := (isClosed_Iic).inter (isClosed_le hΔ.abs continuous_const)
  obtain ⟨n0, hn0, hn0'⟩ := hneg x
  have hSnne : Sn.Nonempty := ⟨n0, hn0, hn0'⟩
  have hSnb : BddAbove Sn := ⟨x, fun p hp => hp.1⟩
  set a := sSup Sn with ha
  have haS : a ∈ Sn := hSnc.csSup_mem hSnne hSnb
  have hax : a < x := lt_of_le_of_ne haS.1 (fun h => by
    have := haS.2; rw [h] at this; linarith)
  have hIoo : Ioo a b ⊆ U := by
    intro y hy
    by_contra hyU
    have hy2 : |Δ y| ≤ 2 := not_lt.mp hyU
    rcases le_total y x with hyx | hxy
    · have : y ∈ Sn := ⟨hyx, hy2⟩
      exact absurd (le_csSup hSnb this) (not_le.mpr hy.1)
    · have : y ∈ Sp := ⟨hxy, hy2⟩
      exact absurd (csInf_le hSpb this) (not_le.mpr hy.2)
  have hxIoo : x ∈ Ioo a b := ⟨hax, hxb⟩
  have hsub : Ioo a b ⊆ connectedComponentIn U x :=
    isPreconnected_Ioo.subset_connectedComponentIn hxIoo hIoo
  have hC : connectedComponentIn U x ⊆ Ioo a b := by
    intro y hy
    have hpre := isPreconnected_connectedComponentIn (F := U) (x := x)
    have hxC : x ∈ connectedComponentIn U x := mem_connectedComponentIn hxU
    have hCU : connectedComponentIn U x ⊆ U := connectedComponentIn_subset _ _
    constructor
    · by_contra hya
      have hya' : y ≤ a := not_lt.mp hya
      have : a ∈ connectedComponentIn U x := hpre.Icc_subset hy hxC ⟨hya', haS.1⟩
      have := hCU this
      have := haS.2
      exact absurd ‹a ∈ U› (not_lt.mpr this)
    · by_contra hyb
      have hyb' : b ≤ y := not_lt.mp hyb
      have : b ∈ connectedComponentIn U x := hpre.Icc_subset hxC hy ⟨hbS.1, hyb'⟩
      have := hCU this
      exact absurd ‹b ∈ U› (not_lt.mpr hbS.2)
  refine ⟨a, b, hax, hxb, subset_antisymm hC hsub, ?_, ?_⟩
  · refine le_antisymm haS.2 ?_
    have hcl : IsClosed {t : ℝ | 2 ≤ |Δ t|} := isClosed_le continuous_const hΔ.abs
    have hsub2 : Ioo a x ⊆ {t : ℝ | 2 ≤ |Δ t|} := fun y hy => (show 2 < |Δ y| from hIoo ⟨hy.1, hy.2.trans hxb⟩).le
    have : a ∈ closure (Ioo a x) := by rw [closure_Ioo hax.ne]; exact ⟨le_refl _, hax.le⟩
    exact hcl.closure_subset_iff.2 hsub2 this
  · refine le_antisymm hbS.2 ?_
    have hcl : IsClosed {t : ℝ | 2 ≤ |Δ t|} := isClosed_le continuous_const hΔ.abs
    have hsub2 : Ioo x b ⊆ {t : ℝ | 2 ≤ |Δ t|} := fun y hy => (show 2 < |Δ y| from hIoo ⟨hax.trans hy.1, hy.2⟩).le
    have : b ∈ closure (Ioo x b) := by rw [closure_Ioo hxb.ne]; exact ⟨hxb.le, le_refl _⟩
    exact hcl.closure_subset_iff.2 hsub2 this

/-! ### Local finiteness of the endpoints -/

/-- If `Δ` is the restriction of an entire function and `|Δ| ≢ 2`, then `{|Δ| = 2}` (which contains every endpoint of every
component of `{|Δ| > 2}`) is finite on every compact interval. -/
theorem finite_endpoints {Δ : ℝ → ℝ} {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hDΔ : ∀ t : ℝ, D (t : ℂ) = (Δ t : ℂ)) (hne : ∃ t, |Δ t| ≠ 2) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ |Δ t| = 2}.Finite := by
  by_contra hinf
  have hinf' : {t : ℝ | t ∈ Icc a b ∧ |Δ t| = 2}.Infinite := hinf
  obtain ⟨x, -, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact (K := Icc a b) isCompact_Icc
    (fun t ht => ht.1)
  rw [accPt_iff_frequently] at hacc
  have hacc' : ∃ᶠ y in 𝓝[≠] x, y ∈ {t : ℝ | t ∈ Icc a b ∧ |Δ t| = 2} := by
    rw [frequently_nhdsWithin_iff]
    exact hacc.mono (fun y hy => ⟨hy.2, hy.1⟩)
  set f : ℂ → ℂ := fun z => D z ^ 2 - 4 with hf
  have hfa : AnalyticOnNhd ℂ f univ := fun z _ => ((hD.pow 2).sub_const 4 |>.analyticAt z)
  have hfreq : ∃ᶠ z in 𝓝[≠] (x : ℂ), f z = 0 := by
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall (fun s hs => by simpa using hs)
    refine ht.frequently (hacc'.mono fun s hs => ?_)
    obtain ⟨-, hs2⟩ := hs
    show D (s : ℂ) ^ 2 - 4 = 0
    rw [hDΔ s]
    have h1 : (Δ s) ^ 2 = 4 := by
      have := sq_abs (Δ s); rw [hs2] at this; linarith
    have : ((Δ s : ℝ) : ℂ) ^ 2 = 4 := by exact_mod_cast h1
    rw [this]; ring
  have hzero := hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ (x : ℂ)) hfreq
  obtain ⟨t0, ht0⟩ := hne
  have h0 := hzero (mem_univ (t0 : ℂ))
  simp only [hf, Pi.zero_apply, hDΔ] at h0
  have h1 : ((Δ t0 : ℝ) : ℂ) ^ 2 = 4 := by linear_combination h0
  have h2 : (Δ t0) ^ 2 = 4 := by exact_mod_cast h1
  apply ht0
  have : |Δ t0| ^ 2 = 2 ^ 2 := by rw [sq_abs]; linarith
  exact (sq_eq_sq₀ (abs_nonneg _) (by norm_num)).1 this

/-! ### Support -/

/-- A measure with continuous nonnegative density `ρ` has support `closure {ρ > 0}`. -/
theorem support_withDensity {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ t, 0 ≤ ρ t) :
    (volume.withDensity (fun t => ENNReal.ofReal (ρ t))).support = closure {t | 0 < ρ t} := by
  set μ : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (ρ t)) with hμ
  have hmeas : Measurable fun t => ENNReal.ofReal (ρ t) := ENNReal.measurable_ofReal.comp hρ.measurable
  ext t
  rw [Measure.support_eq_forall_isOpen]
  constructor
  · intro h
    by_contra hnot
    have hnc : t ∈ (closure {t | 0 < ρ t})ᶜ := hnot
    have hopen : IsOpen (closure {t | 0 < ρ t})ᶜ := isClosed_closure.isOpen_compl
    have := h _ hnc hopen
    have hzero : μ (closure {t | 0 < ρ t})ᶜ = 0 := by
      rw [hμ, withDensity_apply _ hopen.measurableSet]
      refine setLIntegral_eq_zero hopen.measurableSet (fun y hy => ?_)
      have : ¬ 0 < ρ y := fun hp => hy (subset_closure hp)
      have : ρ y = 0 := le_antisymm (not_lt.1 this) (hρ0 y)
      simp [this]
    exact absurd hzero this.ne'
  · intro ht u htu hu
    obtain ⟨y, hyu, hy⟩ : (u ∩ {t | 0 < ρ t}).Nonempty := by
      have := mem_closure_iff.1 ht u hu htu
      simpa [Set.inter_comm] using this
    have hW : IsOpen (u ∩ {t | 0 < ρ t}) := hu.inter (isOpen_lt continuous_const hρ)
    have hWne : (u ∩ {t | 0 < ρ t}).Nonempty := ⟨y, hyu, hy⟩
    have hWpos : 0 < volume (u ∩ {t | 0 < ρ t}) := hW.measure_pos volume hWne
    have hle : μ (u ∩ {t | 0 < ρ t}) ≤ μ u := measure_mono Set.inter_subset_left
    refine lt_of_lt_of_le ?_ hle
    rw [hμ, withDensity_apply _ hW.measurableSet]
    rw [lt_iff_le_and_ne]
    refine ⟨bot_le, fun h0 => ?_⟩
    have h1 := (setLIntegral_eq_zero_iff hW.measurableSet hmeas).1 h0.symm
    have hnull : volume (u ∩ {t | 0 < ρ t}) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h1] with x hx hxW
      have h3 := hx hxW
      have hp : 0 < ρ x := hxW.2
      rw [ENNReal.ofReal_eq_zero] at h3
      linarith
    exact absurd hnull hWpos.ne'

#print axioms connectedComponentIn_eq_Ioo
#print axioms finite_endpoints
#print axioms support_withDensity
#print axioms rootDensity_le

end QuantumNLS.RootDensity
