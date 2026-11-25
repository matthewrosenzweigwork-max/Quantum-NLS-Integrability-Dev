import Mathlib
import QuantumNLS.Local002Analytic

/-! LOCAL-003 stage S3a: real-analyticity of `u ↦ dressedIntegral L κ u n r = (2πi)⁻¹∮(z-p_n)(z-𝓛_u)⁻¹dz` on the
ball `2√κ C_{L,r} ρ ≤ 1`.  Same route as the frozen `Local002.proj_analytic` (read-only, copied proof): the integrand is
the image of `(z - c)·R_0 (1 - T(u))⁻¹` in `C(Γ_n, B(H))`, with the continuous weight `W(z) = (z-c)·1`, under the bounded
contour-integral functional `J`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003DressedAnalytic
open QuantumNLS.LocalSpectral QuantumNLS.Local002

variable {L κ : ℝ}

theorem dressed_analytic (hyp : FreeResolventHyp L κ) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) {ρ : ℝ} (hρ : 2 * Real.sqrt κ * Cconst L r * ρ ≤ 1) :
    AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => dressedIntegral L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  classical
  set c : ℂ := (pm L n : ℂ) with hc
  set K0 : ℝ := 2 * Real.sqrt κ * Cconst L r with hK0def
  have hK0 : 0 ≤ K0 := by
    have := Cconst_nonneg L r
    positivity
  let Rf : ℂ → H2 L →L[ℂ] H2 L := fun z =>
    QuantumNLS.LocalSpectral.resolvent L κ (fun _ => 0) (parity n) z
  have hsph : ∀ z ∈ sphere c r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [hc, mem_sphere_iff_norm] using hz
  have hfree : ∀ z ∈ sphere c r, IsResolvent L κ (fun _ => 0) (parity n) z (Rf z) ∧
      ‖Rf z‖ ≤ 1 / r := fun z hz => by
    obtain ⟨R0, h0, hR⟩ := hyp.res r n z hr hr2 (hsph z hz)
    have : Rf z = R0 := resolvent_eq h0
    rw [this]; exact ⟨h0, hR⟩
  have hex : ∀ z ∈ sphere c r, ∀ u : Lp ℂ 2 (μI L), ∃ T, IsMulOp κ (Rf z) (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ K0 * ‖u‖ := fun z hz u => by
    obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) (Rf z) (u : ℝ → ℂ) (mul_nonneg hK0 (norm_nonneg _))
      (fun φ => by
        obtain ⟨hm, hb⟩ := hyp.pot r n z (Rf z) hr hr2 (hsph z hz) (hfree z hz).1 u φ
        exact ⟨hm, by rw [hK0def]; exact hb⟩)
    exact ⟨T, hTa, hTn⟩
  have hM : 0 ≤ K0 / r := div_nonneg hK0 hr.le
  have hlip : ∀ z ∈ sphere c r, ∀ w ∈ sphere c r, ∀ (u : Lp ℂ 2 (μI L)) (Tz Tw : H2 L →L[ℂ] H2 L),
      IsMulOp κ (Rf z) (u : ℝ → ℂ) Tz → IsMulOp κ (Rf w) (u : ℝ → ℂ) Tw →
        ‖Tz - Tw‖ ≤ K0 / r * ‖u‖ * ‖z - w‖ := fun z hz w hw u Tz Tw hTz hTw => by
    obtain ⟨T', hT', hn⟩ := hex z hz u
    have hTzT : Tz = T' := hTz.unique hT'
    rw [mulop_sub (hfree z hz).1 (hfree w hw).1 hTz hTw, norm_smul]
    have h1 : ‖Tz * Rf w‖ ≤ K0 * ‖u‖ * (1 / r) :=
      (norm_mul_le _ _).trans (mul_le_mul (hTzT ▸ hn) (hfree w hw).2 (norm_nonneg _)
        (mul_nonneg hK0 (norm_nonneg _)))
    calc ‖w - z‖ * ‖Tz * Rf w‖ ≤ ‖w - z‖ * (K0 * ‖u‖ * (1 / r)) := by gcongr
      _ = K0 / r * ‖u‖ * ‖z - w‖ := by rw [norm_sub_rev]; ring
  obtain ⟨G, hG, hGn, hGa⟩ := exists_Tmap Rf hK0 hM hex hlip
  have hcontRf : ContinuousOn Rf (sphere c r) :=
    continuousOn_resolvent _ (M := 1 / r) (by positivity)
      (fun z hz => ⟨Rf z, (hfree z hz).1, (hfree z hz).2⟩)
  let F0 : C(sphere c r, H2 L →L[ℂ] H2 L) := ⟨fun z => Rf z, hcontRf.restrict⟩
  let Wc : C(sphere c r, H2 L →L[ℂ] H2 L) :=
    ⟨fun z => ((z : ℂ) - c) • (1 : H2 L →L[ℂ] H2 L),
      ((continuous_subtype_val.sub continuous_const).smul continuous_const)⟩
  obtain ⟨Jℂ, hJ⟩ := exists_J (L := L) (c := c) hr
  let J := Jℂ.restrictScalars ℝ
  have hunit : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖G u‖ < 1 := fun u hu => by
    have hu' : ‖u‖ < ρ := by simpa using hu
    calc ‖G u‖ ≤ K0 * ‖u‖ := hGn u
      _ < 1 := by
        rcases hK0.eq_or_lt with h | h
        · rw [← h]; norm_num
        · calc K0 * ‖u‖ < K0 * ρ := by gcongr
            _ ≤ 1 := hρ
  have hana : AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => J (Wc * (F0 * Ring.inverse (1 - G u))))
      (ball 0 ρ) := by
    intro u0 hu0
    have h1 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => (1 : C(sphere c r, H2 L →L[ℂ] H2 L)) - G u) u0 :=
      analyticAt_const.sub (hGa u0)
    have h2 : AnalyticAt ℝ (Ring.inverse : C(sphere c r, H2 L →L[ℂ] H2 L) → _)
        (1 - G u0) := by
      have := analyticAt_inverse (𝕜 := ℝ) (Units.oneSub (G u0) (hunit u0 hu0))
      rwa [Units.val_oneSub] at this
    have h3 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => Ring.inverse (1 - G u)) u0 :=
      AnalyticAt.comp (f := fun u : Lp ℂ 2 (μI L) => (1 : C(sphere c r, H2 L →L[ℂ] H2 L)) - G u)
        (x := u0) h2 h1
    have h4 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => F0 * Ring.inverse (1 - G u)) u0 :=
      AnalyticAt.mul (𝕜 := ℝ) (A := C(sphere c r, H2 L →L[ℂ] H2 L)) analyticAt_const h3
    have h5 : AnalyticAt ℝ (fun u : Lp ℂ 2 (μI L) => Wc * (F0 * Ring.inverse (1 - G u))) u0 :=
      AnalyticAt.mul (𝕜 := ℝ) (A := C(sphere c r, H2 L →L[ℂ] H2 L)) analyticAt_const h4
    exact (J.analyticAt _).comp h5
  refine hana.congr isOpen_ball fun u hu => ?_
  have hu' : ‖G u‖ < 1 := hunit u hu
  have hinv : Ring.inverse (1 - G u) = ↑(Units.oneSub (G u) hu')⁻¹ := by
    have := Ring.inverse_unit (M₀ := C(sphere c r, H2 L →L[ℂ] H2 L)) (Units.oneSub (G u) hu')
    rwa [Units.val_oneSub] at this
  have hpt : ∀ z ∈ sphere c r, (z - c) •
      QuantumNLS.LocalSpectral.resolvent L κ (u : ℝ → ℂ) (parity n) z =
      extC (Wc * (F0 * Ring.inverse (1 - G u))) z := by
    intro z hz
    let zz : sphere c r := ⟨z, hz⟩
    have hT : IsMulOp κ (Rf z) (u : ℝ → ℂ) (G u zz) := by
      rw [hG u zz]
      obtain ⟨T, hT, -⟩ := hex z hz u
      exact Mop_spec ⟨T, hT⟩
    have hTn : ‖G u zz‖ < 1 := lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (G u) zz) hu'
    obtain ⟨S, R, h1, h2, hR, hRes, -, -⟩ := resolvent_of_neumann (hfree z hz).1 hT hTn
    rw [resolvent_eq hRes, extC_apply _ hz, hinv]
    have hV : ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz) = S := by
      have e := congrArg (fun K : C(sphere c r, H2 L →L[ℂ] H2 L) => K zz)
        (Units.inv_mul (Units.oneSub (G u) hu'))
      simp only [Units.val_oneSub, ContinuousMap.mul_apply, ContinuousMap.one_apply,
        ContinuousMap.sub_apply] at e
      calc ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz)
          = (↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz *
              ((1 - G u zz) * S) := by rw [h1, mul_one]
        _ = ((↑(Units.oneSub (G u) hu')⁻¹ : C(sphere c r, H2 L →L[ℂ] H2 L)) zz *
              (1 - G u zz)) * S := (mul_assoc _ _ _).symm
        _ = S := by rw [e, one_mul]
    rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply, hV, hR]
    show (z - c) • (Rf z * S) = ((z - c) • (1 : H2 L →L[ℂ] H2 L)) * (Rf z * S)
    rw [smul_mul_assoc, one_mul]
  symm
  unfold dressedIntegral
  have hcen : QuantumNLS.LocalSpectral.center L n = c := rfl
  rw [hcen, circleIntegral.integral_congr hr.le (fun z hz => hpt z hz)]
  exact (hJ _).symm

end QuantumNLS.Local003DressedAnalytic
#print axioms QuantumNLS.Local003DressedAnalytic.dressed_analytic
