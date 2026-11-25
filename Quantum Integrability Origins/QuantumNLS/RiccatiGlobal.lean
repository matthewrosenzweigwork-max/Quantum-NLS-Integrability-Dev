import Mathlib
import QuantumNLS.RiccatiPicardBranch
import QuantumNLS.RiccatiSobolevS
import QuantumNLS.RiccatiChargeLevels

/-!
# R-3FEAD88B stage (c-i)/(c-ii): globalized Riccati branch on the product ball

Frozen inputs (read only): `RiccatiPicardBall.riccatiT`, `riccatiT_fixed_exists_unique`,
`RiccatiPicardBranch.riccati_local_analytic_branch` (a640d592), `RiccatiSobolevS.iotaCLM`,
`RiccatiChargeLevels.lowT`.

Parameters: `βu > 0` is the uniqueness parameter. The selected fixed point `rfG` is the unique
fixed point of `riccatiT (κ/L) (lowT p.1) (lowT p.2)` in the ball of radius `4 βu / Im z`
(sector hypothesis `16|κ| C² βu² ≤ (Im z)²`, product ball `‖p.i‖ < βu`). Because the existence
statement at any smaller radius `B` produces a fixed point of norm `≤ 2B/Im z ≤ 4βu/Im z`,
uniqueness forces `rfG = (that point)`; hence `‖rfG p‖ ≤ 2B/Im z` for every `B ≤ βu` with
`‖p.i‖ ≤ B`. This is the mechanism that lets one global `C = 4βu` serve the `small` and
`unique_small` fields of `LocalOutput` while the expansions run at a smaller radius `B`.

Holomorphy: at each `p0` in the product ball, the local analytic branch `ψ` of
`riccati_local_analytic_branch` (at parameter `Φ p0`, `Φ p = (lowT p.1, lowT p.2)`) agrees with
`rfG` on a neighbourhood of `p0`, so `rfG` is analytic there.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped Classical

namespace QuantumNLS.RiccatiGlobal

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiSobolevS QuantumNLS.RiccatiPicardBranch

/-- `lowT` equals the continuous inclusion `iotaCLM` when `a ≤ S`. -/
theorem lowT_eq_iota {L a S : ℝ} (haS : a ≤ S) (x : Ell2) :
    lowT L a S x = iotaCLM L a S haS x := by
  unfold lowT
  rw [dif_pos haS]
  rfl

/-- The parameter map `p ↦ (lowT p.1, lowT p.2)` as a continuous linear map (`a ≤ S`). -/
def paramCLM {a : ℝ} (L S : ℝ) (haS : a ≤ S) : Ell2 × Ell2 →L[ℂ] Ell2 × Ell2 :=
  ((iotaCLM L a S haS).comp (ContinuousLinearMap.fst ℂ Ell2 Ell2)).prod
    ((iotaCLM L a S haS).comp (ContinuousLinearMap.snd ℂ Ell2 Ell2))

theorem paramCLM_apply {a : ℝ} (L S : ℝ) (haS : a ≤ S) (p : Ell2 × Ell2) :
    paramCLM L S haS p = (lowT L a S p.1, lowT L a S p.2) := by
  rw [lowT_eq_iota haS, lowT_eq_iota haS]
  rfl

/-- The globalized fixed point. Outside the admissible set it is `0` (never used there). -/
def rfG {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (S : ℝ) (κ βu : ℝ) (hβ : 0 < βu) (z : ℂ)
    (p : Ell2 × Ell2) : Ell2 :=
  if h : 0 < z.im ∧ 16 * |κ| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2 ∧ ‖p.1‖ < βu ∧ ‖p.2‖ < βu then
    Classical.choose (riccatiT_fixed_exists_unique hL ha h.1 κ βu hβ h.2.1
      (lowT L a S p.1) (lowT L a S p.2)
      ((norm_lowT_le L a S p.1).trans h.2.2.1.le) ((norm_lowT_le L a S p.2).trans h.2.2.2.le))
  else 0

/-- Spec of `rfG` on the admissible set: fixed, norm bound at radius `2βu`, uniqueness at `4βu`. -/
theorem rfG_spec {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {S : ℝ} {κ βu : ℝ} (hβ : 0 < βu)
    {z : ℂ} (hz : 0 < z.im) (hκ : 16 * |κ| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    {p : Ell2 × Ell2} (h1 : ‖p.1‖ < βu) (h2 : ‖p.2‖ < βu) :
    riccatiT hL ha hz κ (lowT L a S p.1) (lowT L a S p.2) (rfG hL ha S κ βu hβ z p)
        = rfG hL ha S κ βu hβ z p ∧
      ‖rfG hL ha S κ βu hβ z p‖ ≤ 2 * βu / z.im ∧
      ∀ r' : Ell2, ‖r'‖ ≤ 4 * βu / z.im →
        riccatiT hL ha hz κ (lowT L a S p.1) (lowT L a S p.2) r' = r' →
        r' = rfG hL ha S κ βu hβ z p := by
  have hs := Classical.choose_spec (riccatiT_fixed_exists_unique hL ha hz κ βu hβ hκ
    (lowT L a S p.1) (lowT L a S p.2)
    ((norm_lowT_le L a S p.1).trans h1.le) ((norm_lowT_le L a S p.2).trans h2.le))
  have hdef : rfG hL ha S κ βu hβ z p = Classical.choose (riccatiT_fixed_exists_unique hL ha hz κ βu
      hβ hκ (lowT L a S p.1) (lowT L a S p.2)
      ((norm_lowT_le L a S p.1).trans h1.le) ((norm_lowT_le L a S p.2).trans h2.le)) := by
    unfold rfG
    rw [dif_pos ⟨hz, hκ, h1, h2⟩]
  rw [hdef]
  obtain ⟨hn, hf, hu⟩ := hs
  exact ⟨hf, hn, hu⟩

/-- Monotonicity of the ball radius in the bound `2β/Im z ≤ 4β/Im z`. -/
theorem two_div_le_four_div {β t : ℝ} (hβ : 0 < β) (ht : 0 < t) :
    2 * β / t ≤ 4 * β / t := by
  exact div_le_div_of_nonneg_right (by linarith) ht.le

/-- Small-radius identification: for `0 < B ≤ βu` (strictly `B < βu`) and `‖p.i‖ ≤ B`, the
fixed point `rfG p` is the radius-`2B/Im z` fixed point, so its norm is at most `2B/Im z`. -/
theorem rfG_small_radius {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {S : ℝ} {κ βu : ℝ}
    (hβ : 0 < βu) {z : ℂ} (hz : 0 < z.im) (hκ : 16 * |κ| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    {B : ℝ} (hB : 0 < B) (hBu : B < βu) {p : Ell2 × Ell2} (h1 : ‖p.1‖ ≤ B) (h2 : ‖p.2‖ ≤ B) :
    riccatiT hL ha hz κ (lowT L a S p.1) (lowT L a S p.2) (rfG hL ha S κ βu hβ z p)
        = rfG hL ha S κ βu hβ z p ∧
      ‖rfG hL ha S κ βu hβ z p‖ ≤ 2 * B / z.im := by
  have hB2 : B ^ 2 ≤ βu ^ 2 := by nlinarith
  have hκB : 16 * |κ| * Cmul L a ^ 2 * B ^ 2 ≤ z.im ^ 2 := by
    have h16 : (0 : ℝ) ≤ 16 * |κ| * Cmul L a ^ 2 := by positivity
    exact (mul_le_mul_of_nonneg_left hB2 h16).trans hκ
  obtain ⟨r, hr_norm, hr_fix, _⟩ := riccatiT_fixed_exists_unique hL ha hz κ B hB hκB
    (lowT L a S p.1) (lowT L a S p.2)
    ((norm_lowT_le L a S p.1).trans h1) ((norm_lowT_le L a S p.2).trans h2)
  have hpu1 : ‖p.1‖ < βu := lt_of_le_of_lt h1 hBu
  have hpu2 : ‖p.2‖ < βu := lt_of_le_of_lt h2 hBu
  have hr_small : ‖r‖ ≤ 4 * βu / z.im :=
    hr_norm.trans (div_le_div_of_nonneg_right (by linarith) hz.le)
  have hrG : r = rfG hL ha S κ βu hβ z p :=
    (rfG_spec hL ha hβ hz hκ hpu1 hpu2).2.2 r hr_small hr_fix
  rw [← hrG]
  exact ⟨hr_fix, hr_norm⟩

/-- **Holomorphy of the globalized branch.** For `p0` in the product ball `‖p.i‖ < βu`, `rfG`
is analytic at `p0`: it coincides near `p0` with the local analytic branch `ψ` of
`riccati_local_analytic_branch` at the parameter `(lowT p0.1, lowT p0.2)`. -/
theorem rfG_analyticAt {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {S : ℝ} (haS : a ≤ S)
    {κ βu : ℝ} (hβ : 0 < βu) {z : ℂ} (hz : 0 < z.im)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2)
    {p0 : Ell2 × Ell2} (h1 : ‖p0.1‖ < βu) (h2 : ‖p0.2‖ < βu) :
    AnalyticAt ℂ (rfG hL ha S κ βu hβ z) p0 := by
  let Φ : Ell2 × Ell2 → Ell2 × Ell2 := paramCLM L S haS
  have hΦapp : ∀ p : Ell2 × Ell2, Φ p = (lowT L a S p.1, lowT L a S p.2) :=
    fun p => paramCLM_apply L S haS p
  have hΦan : AnalyticAt ℂ Φ p0 := (paramCLM L S haS).analyticAt p0
  have hp0u : ‖(Φ p0).1‖ < βu := by
    rw [hΦapp]
    exact lt_of_le_of_lt (norm_lowT_le L a S p0.1) h1
  have hp0v : ‖(Φ p0).2‖ < βu := by
    rw [hΦapp]
    exact lt_of_le_of_lt (norm_lowT_le L a S p0.2) h2
  obtain ⟨ψ, hψa, hψev⟩ :=
    riccati_local_analytic_branch hL ha hz κ βu hβ hκ (Φ p0) hp0u hp0v
  have hΦcont : Tendsto Φ (𝓝 p0) (𝓝 (Φ p0)) := hΦan.continuousAt
  have hn1 : ∀ᶠ p in 𝓝 p0, ‖p.1‖ < βu := by
    have ht : Tendsto (fun p : Ell2 × Ell2 => ‖p.1‖) (𝓝 p0) (𝓝 ‖p0.1‖) :=
      ((continuous_norm.comp continuous_fst).tendsto p0)
    exact ht.eventually (Iio_mem_nhds h1)
  have hn2 : ∀ᶠ p in 𝓝 p0, ‖p.2‖ < βu := by
    have ht : Tendsto (fun p : Ell2 × Ell2 => ‖p.2‖) (𝓝 p0) (𝓝 ‖p0.2‖) :=
      ((continuous_norm.comp continuous_snd).tendsto p0)
    exact ht.eventually (Iio_mem_nhds h2)
  have hψev' : ∀ᶠ p in 𝓝 p0,
      riccatiT hL ha hz κ (Φ p).1 (Φ p).2 (ψ (Φ p)) = ψ (Φ p) ∧
        ∀ r' : Ell2, ‖r'‖ ≤ 4 * βu / z.im →
          riccatiT hL ha hz κ (Φ p).1 (Φ p).2 r' = r' → r' = ψ (Φ p) :=
    hΦcont.eventually hψev
  have hEq : ∀ᶠ p in 𝓝 p0, ψ (Φ p) = rfG hL ha S κ βu hβ z p := by
    filter_upwards [hn1, hn2, hψev'] with p hp1 hp2 hp
    obtain ⟨hf, hn, hu⟩ := rfG_spec hL ha hβ hz hκ hp1 hp2
    have hsmall : ‖rfG hL ha S κ βu hβ z p‖ ≤ 4 * βu / z.im :=
      hn.trans (two_div_le_four_div hβ hz)
    have e1 : (Φ p).1 = lowT L a S p.1 := congrArg Prod.fst (hΦapp p)
    have e2 : (Φ p).2 = lowT L a S p.2 := congrArg Prod.snd (hΦapp p)
    have hf' : riccatiT hL ha hz κ (Φ p).1 (Φ p).2 (rfG hL ha S κ βu hβ z p)
        = rfG hL ha S κ βu hβ z p := by
      rw [e1, e2]
      exact hf
    exact (hp.2 (rfG hL ha S κ βu hβ z p) hsmall hf').symm
  have hcomp : AnalyticAt ℂ (fun p => ψ (Φ p)) p0 := hψa.comp hΦan
  exact hcomp.congr hEq

/-- Holomorphy on the open product ball `{‖p.1‖ < βu, ‖p.2‖ < βu}`. -/
theorem rfG_analyticOnNhd {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {S : ℝ} (haS : a ≤ S)
    {κ βu : ℝ} (hβ : 0 < βu) {z : ℂ} (hz : 0 < z.im)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2) :
    AnalyticOnNhd ℂ (rfG hL ha S κ βu hβ z) {p : Ell2 × Ell2 | ‖p.1‖ < βu ∧ ‖p.2‖ < βu} :=
  fun _ hp => rfG_analyticAt hL ha haS hβ hz hκ hp.1 hp.2

end QuantumNLS.RiccatiGlobal

#print axioms QuantumNLS.RiccatiGlobal.paramCLM_apply
#print axioms QuantumNLS.RiccatiGlobal.rfG_spec
#print axioms QuantumNLS.RiccatiGlobal.rfG_small_radius
#print axioms QuantumNLS.RiccatiGlobal.rfG_analyticAt
#print axioms QuantumNLS.RiccatiGlobal.rfG_analyticOnNhd
