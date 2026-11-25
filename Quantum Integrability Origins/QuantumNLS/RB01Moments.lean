import Mathlib
import QuantumNLS.RB01CxGauge

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-15: the contour moments on the complexification and their
real-slice identification (source `collective_actions.tex:377-428`: "Define their symmetric functions without
selecting roots: s_{j,n} = (2πi)⁻¹∮_{|w|=3d} w^j ∂_w f_n / f_n dw, α_n = s_{1,n}/2, c_n = (s_{1,n}² − s_{2,n})/2,
τ_n = α_n² − c_n"; eq. `GB01-H` with this `𝒫_n`).

The objects are defined for every complexified field `(u, v)` (`RB01CxGauge.fx`, `cxDisc`):
* `mom κ u v n j = (2πi)⁻¹ ∮_{|w| = 3d} w^j ∂_w fx / fx dw`, `alphaC = mom 1 / 2`, `cC = (mom 1² − mom 2)/2`,
  `tauC = alphaC² − cC`, `PC w = (w − alphaC)² − tauC`, `HC w = (2πi)⁻¹ ∮_{|ξ|=3d} (ξ − w)⁻¹ fx(ξ)/PC(ξ) dξ`.

Real slice (`v = star q`, `κ > 0`, under the hypotheses of `RB01RootCount.factor`, i.e. for `|n| > N`,
`q = t u` near `u₀`), **`real_slice`**: `mom 1 = β₁ + β₂`, `mom 2 = β₁² + β₂²` with `β₁ = b⁻ − p_n`,
`β₂ = b⁺ − p_n` (the exact two roots of `RB01RootCount.root_count`), hence `alphaC = α_n`, `cC = β₁β₂`,
`tauC = τ_n`, `PC = 𝒫_n`, `HC = H_n` (the real-slice objects of RB01RootCount).
Route (recorded): no argument principle is used (Mathlib has none).  With the factorization `f_n = 𝒫_n G`
(`RB01RootCount.dslope_factor`), `G ≠ 0` on the closed disk `|w| ≤ 3d` (maximum modulus applied to `G + L²`
from `RB01RootCount.sphere_bound`), `∂f/f = 1/(w−β₁) + 1/(w−β₂) + G'/G` on the circle; the first two terms
give `2πi β^j` by Cauchy's integral formula and the last integrates to `0` by Cauchy's theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric

namespace QuantumNLS.RB01Moments

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RB01RootPrep (fn freeF dd ε₀ dd_pos)
open QuantumNLS.RB01RootCount (bm bp alpha tau Pn Hn Pn_eq cell_count dslope_factor deriv_zero_of_order_two
  sphere_bound differentiable_fn)
open QuantumNLS.RB01CxGauge (fx fx_star)
open QuantumNLS.PhysicalContinuousBoundary (boundary)
open QuantumNLS.RootGapMultiplicity (Dl hD)

variable {L κ : ℝ} [Fact (0 < L)]

/-- `s_{j,n}(u, v) = (2πi)⁻¹ ∮_{|w|=3d} w^j ∂_w f_n / f_n dw`. -/
def mom (κ : ℝ) (u v : L2T L) (n : ℤ) (j : ℕ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, 3 * dd L), w ^ j * (deriv (fx κ u v n) w / fx κ u v n w)

def alphaC (κ : ℝ) (u v : L2T L) (n : ℤ) : ℂ := mom κ u v n 1 / 2

def cC (κ : ℝ) (u v : L2T L) (n : ℤ) : ℂ := (mom κ u v n 1 ^ 2 - mom κ u v n 2) / 2

def tauC (κ : ℝ) (u v : L2T L) (n : ℤ) : ℂ := alphaC κ u v n ^ 2 - cC κ u v n

def PC (κ : ℝ) (u v : L2T L) (n : ℤ) (w : ℂ) : ℂ := (w - alphaC κ u v n) ^ 2 - tauC κ u v n

def HC (κ : ℝ) (u v : L2T L) (n : ℤ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ ξ in C(0, 3 * dd L), (ξ - w)⁻¹ • (fx κ u v n ξ / PC κ u v n ξ)

theorem fx_star_fun (κ : ℝ) (q : L2T L) (n : ℤ) : fx κ q (star q) n = fn κ q n :=
  funext fun w => fx_star κ q n w

/-- The real-slice moment identity, in the abstract form used below. -/
theorem moment_of_factor {F G : ℂ → ℂ} {β₁ β₂ : ℂ} {r : ℝ} (hr : 0 < r) (hG : Differentiable ℂ G)
    (hfac : ∀ w, F w = (w - β₁) * (w - β₂) * G w) (h1 : ‖β₁‖ < r) (h2 : ‖β₂‖ < r)
    (hG0 : ∀ w ∈ closedBall (0 : ℂ) r, G w ≠ 0) (j : ℕ) :
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(0, r), w ^ j * (deriv F w / F w) = β₁ ^ j + β₂ ^ j := by
  have hFe : F = fun w => ((w - β₁) * (w - β₂)) * G w := funext hfac
  have hP : Differentiable ℂ (fun w : ℂ => (w - β₁) * (w - β₂)) := by fun_prop
  have hderiv : ∀ w, deriv F w = ((w - β₂) + (w - β₁)) * G w + (w - β₁) * (w - β₂) * deriv G w := by
    intro w
    rw [hFe]
    have hPd : HasDerivAt (fun w : ℂ => (w - β₁) * (w - β₂)) ((w - β₂) + (w - β₁)) w := by
      have := ((hasDerivAt_id w).sub_const β₁).mul ((hasDerivAt_id w).sub_const β₂)
      convert this using 1 <;> first | rfl | (simp only [id]; ring)
    exact ((hPd.mul (hG w).hasDerivAt).deriv)
  have hGd : Differentiable ℂ (deriv G) := fun w => ((hG.analyticAt w).deriv).differentiableAt
  have hb1 : β₁ ∈ ball (0 : ℂ) r := by simpa using h1
  have hb2 : β₂ ∈ ball (0 : ℂ) r := by simpa using h2
  have hsph : ∀ w ∈ sphere (0 : ℂ) r, w - β₁ ≠ 0 ∧ w - β₂ ≠ 0 := by
    intro w hw
    have hwn : ‖w‖ = r := by simpa using hw
    constructor
    · intro h; rw [sub_eq_zero] at h; rw [h] at hwn; linarith
    · intro h; rw [sub_eq_zero] at h; rw [h] at hwn; linarith
  have hcongr : EqOn (fun w => w ^ j * (deriv F w / F w))
      (fun w => ((w - β₁)⁻¹ • w ^ j + (w - β₂)⁻¹ • w ^ j) + w ^ j * (deriv G w / G w)) (sphere (0 : ℂ) r) := by
    intro w hw
    obtain ⟨n1, n2⟩ := hsph w hw
    have hGw : G w ≠ 0 := hG0 w (sphere_subset_closedBall hw)
    simp only [smul_eq_mul]
    rw [hderiv w, hfac w]
    field_simp
  rw [circleIntegral.integral_congr hr.le hcongr]
  have hc1 : ContinuousOn (fun w : ℂ => (w - β₁)⁻¹ • w ^ j) (sphere (0 : ℂ) r) :=
    ContinuousOn.smul (f := fun w : ℂ => (w - β₁)⁻¹) (g := fun w : ℂ => w ^ j)
      (ContinuousOn.inv₀ (f := fun w : ℂ => w - β₁) (by fun_prop) (fun w hw => (hsph w hw).1)) (by fun_prop)
  have hc2 : ContinuousOn (fun w : ℂ => (w - β₂)⁻¹ • w ^ j) (sphere (0 : ℂ) r) :=
    ContinuousOn.smul (f := fun w : ℂ => (w - β₂)⁻¹) (g := fun w : ℂ => w ^ j)
      (ContinuousOn.inv₀ (f := fun w : ℂ => w - β₂) (by fun_prop) (fun w hw => (hsph w hw).2)) (by fun_prop)
  have hc3 : ContinuousOn (fun w : ℂ => w ^ j * (deriv G w / G w)) (closedBall (0 : ℂ) r) := by
    refine ContinuousOn.mul (by fun_prop) ?_
    exact ContinuousOn.div hGd.continuous.continuousOn hG.continuous.continuousOn hG0
  have I1 := hc1.circleIntegrable hr.le
  have I2 := hc2.circleIntegrable hr.le
  have I3 := (hc3.mono sphere_subset_closedBall).circleIntegrable hr.le
  rw [circleIntegral.integral_add (f := fun w => (w - β₁)⁻¹ • w ^ j + (w - β₂)⁻¹ • w ^ j) (I1.add I2) I3,
    circleIntegral.integral_add I1 I2]
  have hpow : DifferentiableOn ℂ (fun w : ℂ => w ^ j) (closedBall (0 : ℂ) r) := by fun_prop
  rw [hpow.circleIntegral_sub_inv_smul hb1, hpow.circleIntegral_sub_inv_smul hb2]
  have h0 : (∮ w in C(0, r), w ^ j * (deriv G w / G w)) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty hc3
      (fun w hw => ?_)
    have hw' : w ∈ closedBall (0 : ℂ) r := ball_subset_closedBall hw.1
    exact (differentiableAt_pow j).mul ((hGd w).div (hG w) (hG0 w hw'))
  rw [h0, add_zero, smul_eq_mul, smul_eq_mul]
  have : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  field_simp

/-- **Real-slice identification** of the contour moments and of `PC`, `HC`. -/
theorem real_slice (hκ : 0 < κ) (q : L2T L) (n : ℤ)
    (ha : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fn κ q n w - freeF L w‖ ≤ 6 * ε₀)
    (hb : ∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 10 / 65536 ≤ ‖fn κ q n w‖)
    (hlm : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n - dd L)).re ∈
          Ioo (((n : ℝ) - 1) * Real.pi) ((n : ℝ) * Real.pi))
    (hlp : (boundary hκ q (QuantumNLS.LocalSpectral.pm L n + dd L)).re ∈
          Ioo ((n : ℝ) * Real.pi) (((n : ℝ) + 1) * Real.pi)) :
    mom κ q (star q) n 1 =
        ((bm hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) +
          ((bp hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ∧
    mom κ q (star q) n 2 =
        ((bm hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ^ 2 +
          ((bp hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ^ 2 ∧
    alphaC κ q (star q) n = (alpha hκ q n : ℂ) ∧
    cC κ q (star q) n = ((bm hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) *
          ((bp hκ q n - QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) ∧
    tauC κ q (star q) n = (tau hκ q n : ℂ) ∧
    PC κ q (star q) n = Pn hκ q n ∧
    HC κ q (star q) n = Hn hκ q n := by
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
  have hr : (3 * dd L) ≠ 0 := by positivity
  -- `G` on the outer circle and on the closed disk
  have hcirc : ∀ ξ ∈ sphere (0 : ℂ) (3 * dd L), ‖G ξ + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5 := by
    intro ξ hξ
    have hξn : ‖ξ‖ = 3 * dd L := by simpa using hξ
    obtain ⟨hP0, hbd⟩ := sphere_bound hξn hn1.le hn2.le (ha ξ (by rw [hξn]; linarith))
    have hq : fn κ q n ξ / ((ξ - β₁) * (ξ - β₂)) = G ξ := by
      rw [hfac ξ]; exact mul_div_cancel_left₀ _ hP0
    rw [← hq]; exact hbd
  have hbound : ∀ w ∈ closedBall (0 : ℂ) (3 * dd L), ‖G w + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 5 := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (3 * dd L))
      isBounded_ball (hG.add_const _).diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball (0 : ℂ) hr] at hz
      exact hcirc z hz
    · rw [closure_ball (0 : ℂ) hr]; exact hw
  have hG0 : ∀ w ∈ closedBall (0 : ℂ) (3 * dd L), G w ≠ 0 := by
    intro w hw h0
    have := hbound w hw
    rw [h0, zero_add, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at this
    have : 0 < L ^ 2 := by positivity
    linarith
  have hr0 : 0 < 3 * dd L := by positivity
  have hm : ∀ j : ℕ, mom κ q (star q) n j = β₁ ^ j + β₂ ^ j := by
    intro j
    unfold mom
    rw [fx_star_fun]
    exact moment_of_factor hr0 hG hfac (by linarith) (by linarith) hG0 j
  have hm1 := hm 1
  have hm2 := hm 2
  simp only [pow_one] at hm1
  have hα : alphaC κ q (star q) n = (alpha hκ q n : ℂ) := by
    unfold alphaC alpha
    rw [hm1, hβ₁, hβ₂]; push_cast; ring
  have hc : cC κ q (star q) n = β₁ * β₂ := by
    unfold cC; rw [hm1, hm2]; ring
  have hτ : tauC κ q (star q) n = (tau hκ q n : ℂ) := by
    unfold tauC
    rw [hα, hc]
    unfold alpha tau
    rw [hβ₁, hβ₂]; push_cast; ring
  have hPC : PC κ q (star q) n = Pn hκ q n := by
    funext w
    unfold PC Pn
    rw [hα, hτ]
  refine ⟨hm1, hm2, hα, hc, hτ, hPC, ?_⟩
  funext w
  unfold HC Hn
  rw [hPC, fx_star_fun]

end QuantumNLS.RB01Moments

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01Moments.moment_of_factor
#print axioms QuantumNLS.RB01Moments.real_slice
