import Mathlib
import QuantumNLS.Local021RSetting

/-!
# LOCAL-021 repair, stage R4: charts at every coupling, by scaling from a fixed unit-coupling chart

Source (`local_transform.tex:104-108`, `local_covariance.tex:197-205`): "At coupling `κ` use the same construction after the scaling `u ↦ √κ u`, and hence the radius `d_L/√κ`";
"`ζ_κ(u) = κ^{-1/2} ζ_1(√κ u)` and the inverse has the same relation."

`Chart.scaled Ch1 hs hκ hκs F` : from a unit-coupling chart `Ch1` (`ζ̃_1` analytic with analytic inverse `η_1` on `B_{R_1}`), a scale `s > 0`, `κ = 1·s²` and ANY LOCAL-020 family `F` at coupling `κ`
(radius `ρ_κ`), the chart at coupling `κ` on `B_{R_κ}`, `R_κ = min (ρ_κ, R_1/s)`, with `ζ̃_κ(x) = s^{-1} ζ̃_1(s x)` (this is the scaling clause of LOCAL-020, `zetaK_scale`) and `η_κ(y) = s^{-1} η_1(s y)`.
`Chart.atCoupling` is the same with `s = √κ`.  `Chart.exists_setting` : every chart carries a constructed `Setting` (`Local021RSetting`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction

namespace QuantumNLS.Local021R

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021

variable {L r : ℝ} [Fact (0 < L)]

/-- `ζ̃_1(s x) = s ζ̃_κ(x)` for `κ = 1·s²` (LOCAL-020 scaling clause, in Fourier variables). -/
theorem zt_scale_chart (Ch1 : Chart L 1 r one_pos) {s : ℝ} (hs : 0 < s) {κ : ℝ} (hκ : 0 < κ) (hκs : κ = 1 * s ^ 2)
    {ρ₂ C₂ : ℝ} (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂) {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ}
    {rr₂ : L2T L → (ℤ →ᵇ ℝ)} (F₂ : Fam020 L κ r ρ₂ C₂ hκ a₂ b₂ rr₂) {x : K} (hx₂ : ‖x‖ < ρ₂)
    (hx : s * ‖x‖ < Ch1.ρ) : Ch1.zt (s • x) = s • zetaT L κ b₂ rr₂ x := by
  subst hκs
  unfold Chart.zt zetaT
  have e : s • x = (s : ℂ) • x := (Complex.coe_smul s x).symm
  rw [e, map_smul]
  have hu₂ : ‖(fourierL2 L).symm x‖ < ρ₂ := by rwa [LinearIsometryEquiv.norm_map]
  have hu : s * ‖(fourierL2 L).symm x‖ < Ch1.ρ := by rwa [LinearIsometryEquiv.norm_map]
  rw [zetaK_scale Ch1.fam hs hκ hρ₂ hC₂ F₂ hu₂ hu, Complex.coe_smul]
  rfl

theorem analyticAt_smul_id (s : ℝ) (x : K) : AnalyticAt ℝ (fun x : K => s • x) x := by
  have e : (fun x : K => s • x) = ⇑(s • ContinuousLinearMap.id ℝ K) := by ext x; simp
  rw [e]; exact ContinuousLinearMap.analyticAt _ x

section Aux

variable (Ch1 : Chart L 1 r one_pos) {s : ℝ} (hs : 0 < s) {κ : ℝ} (hκ : 0 < κ) (hκs : κ = 1 * s ^ 2)
  {ρ₂ C₂ : ℝ} (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂) {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ}
  {rr₂ : L2T L → (ℤ →ᵇ ℝ)} (F₂ : Fam020 L κ r ρ₂ C₂ hκ a₂ b₂ rr₂)

include hs in
theorem scaleR_mem {x : K} (hx : x ∈ ball (0 : K) (min ρ₂ (Ch1.R / s))) : ‖x‖ < ρ₂ ∧ s * ‖x‖ < Ch1.R := by
  have h := mem_ball_zero_iff.1 hx
  refine ⟨lt_of_lt_of_le h (min_le_left _ _), ?_⟩
  have := lt_of_lt_of_le h (min_le_right _ _)
  rwa [lt_div_iff₀ hs, mul_comm] at this

include hs in
theorem smul_mem_scaleR {x : K} (hx : x ∈ ball (0 : K) (min ρ₂ (Ch1.R / s))) : s • x ∈ ball (0 : K) Ch1.R := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact (scaleR_mem Ch1 hs hx).2

include hs hκs hρ₂ hC₂ F₂ in
theorem zeta_scaled {x : K} (hx : x ∈ ball (0 : K) (min ρ₂ (Ch1.R / s))) :
    zetaT L κ b₂ rr₂ x = s⁻¹ • Ch1.zt (s • x) := by
  have h := zt_scale_chart Ch1 hs hκ hκs hρ₂ hC₂ F₂ (scaleR_mem Ch1 hs hx).1
    ((scaleR_mem Ch1 hs hx).2.trans_le Ch1.hRρ)
  rw [h, inv_smul_smul₀ hs.ne']

include hs in
theorem norm_eta_scaled {y : K} (hy : y ∈ ball (0 : K) (min ρ₂ (Ch1.R / s))) :
    ‖s⁻¹ • Ch1.η (s • y)‖ = ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, Ch1.norm_eta (smul_mem_scaleR Ch1 hs hy), norm_smul,
    Real.norm_eq_abs, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

include hs in
theorem eta_scaled_mem {y : K} (hy : y ∈ ball (0 : K) (min ρ₂ (Ch1.R / s))) :
    s⁻¹ • Ch1.η (s • y) ∈ ball (0 : K) (min ρ₂ (Ch1.R / s)) := by
  rw [mem_ball_zero_iff, norm_eta_scaled Ch1 hs hy]; exact mem_ball_zero_iff.1 hy

end Aux

/-- the chart at coupling `κ = 1·s²`, scaled from the unit-coupling chart. -/
def Chart.scaled (Ch1 : Chart L 1 r one_pos) {s : ℝ} (hs : 0 < s) {κ : ℝ} (hκ : 0 < κ) (hκs : κ = 1 * s ^ 2)
    {ρ₂ C₂ : ℝ} (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂) {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ}
    {rr₂ : L2T L → (ℤ →ᵇ ℝ)} (F₂ : Fam020 L κ r ρ₂ C₂ hκ a₂ b₂ rr₂) : Chart L κ r hκ where
  ρ := ρ₂
  C := C₂
  a := a₂
  b := b₂
  rr := rr₂
  hρ := hρ₂
  hC := hC₂
  fam := F₂
  R := min ρ₂ (Ch1.R / s)
  hR := lt_min hρ₂ (div_pos Ch1.hR hs)
  hRρ := min_le_left _ _
  η := fun y => s⁻¹ • Ch1.η (s • y)
  zeta_an := by
    have han : AnalyticOnNhd ℝ (fun x : K => s⁻¹ • Ch1.zt (s • x)) (ball (0 : K) (min ρ₂ (Ch1.R / s))) := by
      intro x hx
      have h1 : AnalyticAt ℝ Ch1.zt (s • x) := Ch1.zeta_an _ (smul_mem_scaleR Ch1 hs hx)
      have h2 : AnalyticAt ℝ (fun x : K => s • x) x := analyticAt_smul_id s x
      exact AnalyticAt.const_smul (c := s⁻¹) (f := fun x : K => Ch1.zt (s • x)) (h1.comp h2)
    exact han.congr isOpen_ball fun x hx => (zeta_scaled Ch1 hs hκ hκs hρ₂ hC₂ F₂ hx).symm
  eta_an := by
    intro y hy
    have h1 : AnalyticAt ℝ Ch1.η (s • y) := Ch1.eta_an _ (smul_mem_scaleR Ch1 hs hy)
    have h2 : AnalyticAt ℝ (fun x : K => s • x) y := analyticAt_smul_id s y
    exact AnalyticAt.const_smul (c := s⁻¹) (f := fun y : K => Ch1.η (s • y)) (h1.comp h2)
  eta_mem := fun y hy => eta_scaled_mem Ch1 hs hy
  zeta_eta := by
    intro y hy
    have hx := eta_scaled_mem Ch1 hs hy
    rw [zeta_scaled Ch1 hs hκ hκs hρ₂ hC₂ F₂ hx, smul_inv_smul₀ hs.ne']
    have := Ch1.zeta_eta (s • y) (smul_mem_scaleR Ch1 hs hy)
    have e : Ch1.zt (Ch1.η (s • y)) = s • y := this
    rw [e, inv_smul_smul₀ hs.ne']
  eta_zeta := by
    intro x hx
    rw [zeta_scaled Ch1 hs hκ hκs hρ₂ hC₂ F₂ hx, smul_inv_smul₀ hs.ne']
    have := Ch1.eta_zeta (s • x) (smul_mem_scaleR Ch1 hs hx)
    have e : Ch1.η (Ch1.zt (s • x)) = s • x := this
    show s⁻¹ • Ch1.η (Ch1.zt (s • x)) = x
    rw [e, inv_smul_smul₀ hs.ne']

/-- the chart at an arbitrary coupling `κ > 0`, scaled from the unit-coupling chart with `s = √κ`. -/
def Chart.atCoupling (Ch1 : Chart L 1 r one_pos) {κ : ℝ} (hκ : 0 < κ) {ρ₂ C₂ : ℝ} (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂)
    {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ} {rr₂ : L2T L → (ℤ →ᵇ ℝ)}
    (F₂ : Fam020 L κ r ρ₂ C₂ hκ a₂ b₂ rr₂) : Chart L κ r hκ :=
  Chart.scaled Ch1 (Real.sqrt_pos.2 hκ) hκ (by rw [Real.sq_sqrt hκ.le]; ring) hρ₂ hC₂ F₂

/-- every chart carries a constructed `Setting`, built on the same family. -/
theorem Chart.exists_setting {κ : ℝ} {hκ : 0 < κ} (Ch : Chart L κ r hκ) :
    ∃ S : Setting L κ r hκ, S.ρ = Ch.ρ ∧ S.C = Ch.C ∧ S.a = Ch.a ∧ S.b = Ch.b ∧ S.rr = Ch.rr := by
  obtain ⟨Rs, Cq, h0, h1, h2, h3, h4⟩ := Ch.exists_radius
  exact ⟨Ch.toSetting Rs Cq h0 h1 h2 h4, rfl, rfl, rfl, rfl, rfl⟩

end QuantumNLS.Local021R

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021R.zt_scale_chart
#print axioms QuantumNLS.Local021R.Chart.scaled
#print axioms QuantumNLS.Local021R.Chart.atCoupling
#print axioms QuantumNLS.Local021R.Chart.exists_setting
