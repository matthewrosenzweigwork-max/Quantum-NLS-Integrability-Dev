import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALLaurent38

/-! Batch 38, L02b-2: local joint analyticity of the complexified exterior branch
`g = (T + √D)/2` and of `ℓ = log g` near `(ζ, a, b) = (0, α₀, conj α₀)`, and agreement with
`alLog38` on the real slice (paper/v2.tex D:thm:ALfinite, proof l.1969).

`D = T² - 4ζ^{2L}`, `√D := D ^ (1/2)` (principal), `g = (T + √D)/2`, `ℓ = Complex.log g`.
Near `(0, α₀, conj α₀)`: `T ≈ e^{M/2} > 0`, so `D` and `g` lie in the slit plane. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Filter Topology Metric Set

/-- `D(ζ; a, b) = T² - 4 ζ^{2L}`. -/
def alComplexD38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  alComplexT38 a b ζ ^ 2 - 4 * ζ ^ (2 * L)

/-- Principal square root of `D`. -/
def alComplexS38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  alComplexD38 a b ζ ^ ((2 : ℂ)⁻¹)

/-- `g = (T + √D)/2`. -/
def alComplexG38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  (alComplexT38 a b ζ + alComplexS38 a b ζ) / 2

/-- `ℓ = log g` (principal). -/
def alComplexLog38 {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) : ℂ :=
  Complex.log (alComplexG38 a b ζ)

/-! ### Analyticity at a point -/

theorem analyticAt_alComplexD38 {L : ℕ} [NeZero L] (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ))
    (hq : q.2 ∈ alComplexDomain38 L) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexD38 r.2.1 r.2.2 r.1) q := by
  have hT := analyticAt_alComplexT38 q hq
  have hz : AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => r.1) q :=
    (ContinuousLinearMap.fst ℂ ℂ ((ZMod L → ℂ) × (ZMod L → ℂ))).analyticAt q
  unfold alComplexD38
  exact (hT.pow 2).sub (analyticAt_const.mul (hz.pow _))

theorem analyticAt_alComplexS38 {L : ℕ} [NeZero L] (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ))
    (hq : q.2 ∈ alComplexDomain38 L) (hD : alComplexD38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexS38 r.2.1 r.2.2 r.1) q := by
  unfold alComplexS38
  exact (analyticAt_alComplexD38 q hq).cpow analyticAt_const hD

theorem analyticAt_alComplexG38 {L : ℕ} [NeZero L] (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ))
    (hq : q.2 ∈ alComplexDomain38 L) (hD : alComplexD38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexG38 r.2.1 r.2.2 r.1) q := by
  unfold alComplexG38
  exact ((analyticAt_alComplexT38 q hq).add (analyticAt_alComplexS38 q hq hD)).div_const

theorem analyticAt_alComplexLog38 {L : ℕ} [NeZero L] (q : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ))
    (hq : q.2 ∈ alComplexDomain38 L) (hD : alComplexD38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane)
    (hG : alComplexG38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) => alComplexLog38 r.2.1 r.2.2 r.1) q := by
  unfold alComplexLog38
  exact (analyticAt_alComplexG38 q hq hD).clog hG

theorem exp_alComplexLog38 {L : ℕ} {a b : ZMod L → ℂ} {ζ : ℂ}
    (hG : alComplexG38 a b ζ ∈ Complex.slitPlane) :
    Complex.exp (alComplexLog38 a b ζ) = alComplexG38 a b ζ :=
  Complex.exp_log (Complex.slitPlane_ne_zero hG)

/-! ### Real slice -/

theorem alComplexD38_real {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (ζ : ℂ) :
    alComplexD38 α (fun j => star (α j)) ζ = alExtD38 α ζ := by
  unfold alComplexD38 alExtD38
  rw [alComplexT38_real hα]

theorem cpow_sq_half38 {c : ℝ} (hc : 0 < c) :
    (((c : ℂ)) ^ 2) ^ ((2 : ℂ)⁻¹) = (c : ℂ) := by
  have h1 : ((c : ℂ)) ^ 2 = ((c ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2, ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [← one_div, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_sq hc.le

theorem alComplexS38_real_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alComplexS38 α (fun j => star (α j)) 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alComplexS38
  rw [alComplexD38_real hα, alExtD38_zero hα]
  exact cpow_sq_half38 (Real.exp_pos _)

theorem alComplexG38_real_zero {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alComplexG38 α (fun j => star (α j)) 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  unfold alComplexG38
  rw [alComplexS38_real_zero hα, alComplexT38_real hα, alExtT38_zero hα]; ring

theorem alComplexD38_real_zero_mem {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alComplexD38 α (fun j => star (α j)) 0 ∈ Complex.slitPlane := by
  rw [alComplexD38_real hα, alExtD38_zero hα, ← Complex.ofReal_pow]
  exact Complex.ofReal_mem_slitPlane.2 (by positivity)

theorem alComplexG38_real_zero_mem {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alComplexG38 α (fun j => star (α j)) 0 ∈ Complex.slitPlane := by
  rw [alComplexG38_real_zero hα]
  exact Complex.ofReal_mem_slitPlane.2 (Real.exp_pos _)

/-- Identification with the real-slice objects on a ball `ρ ≤ 1`, given the slit conditions. -/
theorem alComplexLog38_real {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexD38 α (fun j => star (α j)) ζ ∈ Complex.slitPlane)
    (hG : ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexG38 α (fun j => star (α j)) ζ ∈ Complex.slitPlane) :
    ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexLog38 α (fun j => star (α j)) ζ = alLog38 α ζ := by
  have hsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) 1 := ball_subset_ball hρ1
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
  have hconn : IsPreconnected (ball (0 : ℂ) ρ) := (convex_ball _ _).isPreconnected
  obtain ⟨hsA, hsq, hs0⟩ := alExtS38_spec hα
  set c : ℂ := ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast (Real.exp_pos _).ne'
  -- the principal root
  have hSan : AnalyticOnNhd ℂ (alComplexS38 α (fun j => star (α j))) (ball (0 : ℂ) ρ) := by
    intro ζ hζ
    unfold alComplexS38
    have : AnalyticAt ℂ (alComplexD38 α (fun j => star (α j))) ζ := by
      have e : alComplexD38 α (fun j => star (α j)) = alExtD38 α := funext (alComplexD38_real hα)
      rw [e]; exact (alExtD38_differentiable α).analyticAt ζ
    exact this.cpow analyticAt_const (hD ζ hζ)
  have hSsq : ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexS38 α (fun j => star (α j)) ζ ^ 2 = alExtD38 α ζ := by
    intro ζ hζ
    unfold alComplexS38
    rw [Complex.cpow_ofNat_inv_pow, alComplexD38_real hα]
  have hS0 : alComplexS38 α (fun j => star (α j)) 0 = c := alComplexS38_real_zero hα
  have hSeq : ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexS38 α (fun j => star (α j)) ζ = alExtS38 α ζ := by
    set s1 := alComplexS38 α (fun j => star (α j))
    have hs' : AnalyticOnNhd ℂ (alExtS38 α) (ball (0 : ℂ) ρ) := hsA.mono hsub
    have hu : AnalyticOnNhd ℂ (fun z => s1 z - alExtS38 α z) (ball (0 : ℂ) ρ) := hSan.sub hs'
    have hv : AnalyticOnNhd ℂ (fun z => s1 z + alExtS38 α z) (ball (0 : ℂ) ρ) := hSan.add hs'
    have hprod : ∀ z ∈ ball (0 : ℂ) ρ, (s1 z - alExtS38 α z) * (s1 z + alExtS38 α z) = 0 := by
      intro z hz
      have h1 := hSsq z hz
      have h2 := hsq z (hsub hz)
      linear_combination h1 - h2
    have hv0 : s1 0 + alExtS38 α 0 ≠ 0 := by
      rw [hS0, hs0]; intro h; apply hc0; linear_combination h / 2
    have hvev : ∀ᶠ z in 𝓝 (0 : ℂ), s1 z + alExtS38 α z ≠ 0 :=
      (hv 0 h00).continuousAt.eventually_ne hv0
    have hin : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) ρ := isOpen_ball.mem_nhds h00
    have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), s1 z - alExtS38 α z = 0 := by
      refine (((hvev.and hin).filter_mono (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))).frequently).mono ?_
      rintro z ⟨h1, h2⟩
      exact (mul_eq_zero.mp (hprod z h2)).resolve_right h1
    intro ζ hζ
    have := hu.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn h00 hfr hζ
    simpa [sub_eq_zero] using this
  have hGeq : ∀ ζ ∈ ball (0 : ℂ) ρ,
      alComplexG38 α (fun j => star (α j)) ζ = alExteriorG38 α ζ := by
    intro ζ hζ
    unfold alComplexG38 alExteriorG38
    rw [alComplexT38_real hα, hSeq ζ hζ]
  -- the logarithms
  set ℓ1 := alComplexLog38 α (fun j => star (α j)) with hℓ1
  have hℓan : AnalyticOnNhd ℂ ℓ1 (ball (0 : ℂ) ρ) := by
    intro ζ hζ
    have hGan : AnalyticAt ℂ (alComplexG38 α (fun j => star (α j))) ζ := by
      refine (alExteriorG38_analytic hα ζ (hsub hζ)).congr ?_
      filter_upwards [isOpen_ball.mem_nhds hζ] with z hz using (hGeq z hz).symm
    exact hGan.clog (hG ζ hζ)
  have hexp : ∀ ζ ∈ ball (0 : ℂ) ρ, Complex.exp (ℓ1 ζ) = alExteriorG38 α ζ := by
    intro ζ hζ
    rw [hℓ1, exp_alComplexLog38 (hG ζ hζ), hGeq ζ hζ]
  obtain ⟨hA, hE, hA0, -⟩ := alLog38_spec hα
  have hl0 : ℓ1 0 = alLog38 α 0 := by
    rw [hA0, hℓ1]
    unfold alComplexLog38
    rw [alComplexG38_real_zero hα, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  -- d = ℓ1 - alLog38 is constant
  have hdan : AnalyticOnNhd ℂ (fun z => ℓ1 z - alLog38 α z) (ball (0 : ℂ) ρ) :=
    hℓan.sub (hA.mono hsub)
  have hdd : ∀ z ∈ ball (0 : ℂ) ρ, HasDerivAt (fun z => ℓ1 z - alLog38 α z)
      (deriv (fun z => ℓ1 z - alLog38 α z) z) z := fun z hz =>
    (hdan z hz).differentiableAt.hasDerivAt
  have hdz : ∀ z ∈ ball (0 : ℂ) ρ, deriv (fun z => ℓ1 z - alLog38 α z) z = 0 := by
    intro z hz
    have h1 := (hdd z hz).cexp
    have h2 : HasDerivAt (fun z => Complex.exp (ℓ1 z - alLog38 α z)) 0 z := by
      refine (hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      rw [Complex.exp_sub, hexp y hy, hE y (hsub hy)]
      exact div_self (alExteriorG38_ne_zero hα (hsub hy))
    have h3 := h1.unique h2
    have hne : Complex.exp (ℓ1 z - alLog38 α z) ≠ 0 := Complex.exp_ne_zero _
    exact (mul_eq_zero.mp h3).resolve_left hne
  intro ζ hζ
  have := isOpen_ball.is_const_of_deriv_eq_zero hconn
    (fun y hy => (hdd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => hdz y hy) hζ h00
  have h' : ℓ1 ζ - alLog38 α ζ = ℓ1 0 - alLog38 α 0 := this
  rw [hl0, sub_self] at h'
  exact sub_eq_zero.mp h'

/-! ### Main local statement -/

/-- Local analytic exterior log near a real-slice point.  For `α₀` admissible there are an open
`U ∋ (α₀, conj α₀)` inside the slit-plane domain and `0 < ρ₁ ≤ 1` such that on `ball 0 ρ₁ × U`,
`D` and `g` lie in the slit plane (so `D ≠ 0`, `g ≠ 0`, `exp ℓ = g`), `D, √D, g, ℓ` are jointly
analytic in `(ζ, a, b)` at every point of `ball 0 ρ₁ × U`, and on every real-slice point of `U`,
`ℓ(ζ; α, conj α) = alLog38 α ζ` for `ζ ∈ ball 0 ρ₁`. -/
theorem exists_alComplexLogNhd38 {L : ℕ} [NeZero L] {α₀ : ZMod L → ℂ} (hα₀ : IsALField38 α₀) :
    ∃ (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))) (ρ₁ : ℝ),
      IsOpen U ∧ (α₀, fun j => star (α₀ j)) ∈ U ∧ U ⊆ alComplexDomain38 L ∧
      0 < ρ₁ ∧ ρ₁ ≤ 1 ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        alComplexD38 p.1 p.2 ζ ∈ Complex.slitPlane ∧ alComplexG38 p.1 p.2 ζ ∈ Complex.slitPlane) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        AnalyticAt ℂ (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
          alComplexLog38 r.2.1 r.2.2 r.1) (ζ, p)) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ U,
        Complex.exp (alComplexLog38 p.1 p.2 ζ) = alComplexG38 p.1 p.2 ζ) ∧
      (∀ α : ZMod L → ℂ, IsALField38 α → (α, fun j => star (α j)) ∈ U →
        ∀ ζ ∈ ball (0 : ℂ) ρ₁, alComplexLog38 α (fun j => star (α j)) ζ = alLog38 α ζ) := by
  set p₀ : (ZMod L → ℂ) × (ZMod L → ℂ) := (α₀, fun j => star (α₀ j)) with hp₀
  have hd₀ : p₀ ∈ alComplexDomain38 L := alRealSlice_mem_domain38 hα₀
  set q₀ : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) := (0, p₀) with hq₀
  have hdomO : IsOpen (alComplexDomain38 L) := isOpen_alComplexDomain38 L
  -- eventual conditions near q₀
  have e1 : ∀ᶠ q in 𝓝 q₀, q.2 ∈ alComplexDomain38 L :=
    (hdomO.preimage continuous_snd).mem_nhds hd₀
  have hDc : ContinuousAt (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
      alComplexD38 r.2.1 r.2.2 r.1) q₀ := (analyticAt_alComplexD38 q₀ hd₀).continuousAt
  have hD0 : alComplexD38 p₀.1 p₀.2 0 ∈ Complex.slitPlane := alComplexD38_real_zero_mem hα₀
  have e2 : ∀ᶠ q in 𝓝 q₀, alComplexD38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane :=
    hDc.eventually (Complex.isOpen_slitPlane.mem_nhds hD0)
  have hGc : ContinuousAt (fun r : ℂ × (ZMod L → ℂ) × (ZMod L → ℂ) =>
      alComplexG38 r.2.1 r.2.2 r.1) q₀ := (analyticAt_alComplexG38 q₀ hd₀ hD0).continuousAt
  have hG0 : alComplexG38 p₀.1 p₀.2 0 ∈ Complex.slitPlane := alComplexG38_real_zero_mem hα₀
  have e3 : ∀ᶠ q in 𝓝 q₀, alComplexG38 q.2.1 q.2.2 q.1 ∈ Complex.slitPlane :=
    hGc.eventually (Complex.isOpen_slitPlane.mem_nhds hG0)
  have hev := (e1.and e2).and e3
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hev
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hu
  obtain ⟨V, hVv, hVo, hVp⟩ := _root_.mem_nhds_iff.1 hv
  have hVd : V ⊆ alComplexDomain38 L := fun p hp =>
    (huv (Set.mk_mem_prod (hball (mem_ball_self hρ)) (hVv hp))).1.1
  set ρ₁ : ℝ := min ρ 1 with hρ₁
  have hρ₁pos : 0 < ρ₁ := lt_min hρ one_pos
  have hmem : ∀ ζ ∈ ball (0 : ℂ) ρ₁, ∀ p ∈ V,
      p ∈ alComplexDomain38 L ∧ alComplexD38 p.1 p.2 ζ ∈ Complex.slitPlane ∧
        alComplexG38 p.1 p.2 ζ ∈ Complex.slitPlane := by
    intro ζ hζ p hp
    have hζ' : ζ ∈ u := hball (ball_subset_ball (min_le_left _ _) hζ)
    have := huv (Set.mk_mem_prod hζ' (hVv hp))
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨V, ρ₁, hVo, hVp, hVd, hρ₁pos, min_le_right _ _,
    fun ζ hζ p hp => (hmem ζ hζ p hp).2, ?_, ?_, ?_⟩
  · intro ζ hζ p hp
    obtain ⟨h1, h2, h3⟩ := hmem ζ hζ p hp
    exact analyticAt_alComplexLog38 (ζ, p) h1 h2 h3
  · intro ζ hζ p hp
    exact exp_alComplexLog38 (hmem ζ hζ p hp).2.2
  · intro α hα hαV
    exact alComplexLog38_real hα hρ₁pos (min_le_right _ _)
      (fun ζ hζ => (hmem ζ hζ _ hαV).2.1) (fun ζ hζ => (hmem ζ hζ _ hαV).2.2)

end NlsGge.AblowitzLadik

end
