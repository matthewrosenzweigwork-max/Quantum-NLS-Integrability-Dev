import Mathlib
import QuantumNLS.Local021RFinal

/-!
# LOCAL-021 repair, stage R6: the repaired headline `QuantumNLS.Local021Repair.reset_moser_covariance_full`

Source: `local_covariance.tex:134` (`prop:reset-moser-covariance`); the intended argument for the Moser hypotheses is `local_transform.tex:152`.

**Premises** (exactly the printed ones): `[Fact (0 < L)]`; `0 < r < 2π/L` (the LOCAL-003/LOCAL-007 contour radius, as in the frozen LOCAL-020/LOCAL-021 headlines); and `FullDiffeoPremise L r` ("the preceding exact-modulus family is a full analytic
diffeomorphism between Hilbert balls", stated for the unit-coupling LOCAL-020 family; the premise at coupling `κ` is the scaled one, `Local021RScale.Chart.scaled`).  No `Setting` parameter and no other added hypothesis.

**Conclusions** for the actual chart (`ζ` of LOCAL-020, `Φ = S⁻¹ ∘ ζ` of LOCAL-017's procedure):
* (0) the exact-modulus family exists at every coupling (LOCAL-020);
* (1) at every coupling `κ`, on EVERY LOCAL-020 family there is a `Setting` (constructed, not assumed: its `PrintedHyp` discharged from R-507DD869/LOCAL-016/`norm_zeta_sq`) with all printed per-setting conclusions `SettingProps`
  (procedure outputs and flow, six covariances of `Ω`, radial/Haar primitive, Moser field, `S`, `S⁻¹`, `Φ` with index forms, plane normalization, `DΦ(0) = 𝓕`);
* (2) the scaling identities `Ω_{sy}^A = Ω_y^B`, `f^A(sz) = s²f^B(z)`, `Y^A_t(sz) = sY^B_t(z)`, `S^A(sz) = sS^B(z)`, `Φ_A(su) = sΦ_B(u)` between the (constructed) settings at couplings `κ` and `κ s²`;
* (3) a constant `C_L ≥ 0` (chosen before, hence independent of, the unit-coupling family, the ball radius `ρ₀`, `κ` and `u`; it comes from the unit chart and transfers between unit-coupling settings by uniqueness of the canonical map on common domains);
  for every unit-coupling family: the fixed unit chart `S₁` with radius `r_* ≤ r_M(S₁)`; the chart at coupling `κ` has the scaled domain `{√κ‖u‖ < r_*}` (ball of radius `r_*/√κ`) and the map `Φ̂_κ(u) = κ^{-1/2}Φ_1(√κ u)`,
  which agrees with the procedure's `Φ_κ` of every (constructed) setting at coupling `κ` on the common domain; every fixed `L²` ball `‖u‖ < ρ₀` lies in the scaled domain once `κ < (r_*/ρ₀)²`, and there
  `Φ̂_κ` is differentiable, `‖DΦ̂_κ(u) − 𝓕‖ ≤ C_L κ‖u‖²` and (by integrating along `[0,u]`) `‖Φ̂_κ(u) − 𝓕u‖ ≤ C_L κ‖u‖³`, with `C_L` independent of Fourier support; and `Φ̂_κ(su) = sΦ̂_{κs²}(u)`.
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

namespace QuantumNLS.Local021Repair

open QuantumNLS.D01LocalPrimitive QuantumNLS.ResetMoser
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local021
open QuantumNLS.Local021R

variable {L r : ℝ} [Fact (0 < L)]

/-- the unit-coupling chart exists under the printed premise (the family is `fam020_exists` at coupling `1`, LOCAL-020). -/
theorem unit_chart (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (hdiff : FullDiffeoPremise L r) :
    Nonempty (Chart L 1 r one_pos) := by
  obtain ⟨ρ, hρ, C, hC, a, b, rr, F⟩ := fam020_exists (L := L) one_pos hr hr2
  obtain ⟨R, hR, hRρ, η, h1, h2, h3, h4, h5⟩ := hdiff ρ C a b rr hρ hC F
  exact ⟨⟨ρ, C, a, b, rr, hρ, hC, F, R, hR, hRρ, η, h1, h2, h3, h4, h5⟩⟩

theorem unit_chart_of_family (hdiff : FullDiffeoPremise L r) {ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}
    {rr : L2T L → (ℤ →ᵇ ℝ)} (hρ : 0 < ρ) (hC : 0 ≤ C) (F : Fam020 L 1 r ρ C one_pos a b rr) :
    ∃ Ch : Chart L 1 r one_pos, Ch.ρ = ρ ∧ Ch.C = C ∧ Ch.a = a ∧ Ch.b = b ∧ Ch.rr = rr := by
  obtain ⟨R, hR, hRρ, η, h1, h2, h3, h4, h5⟩ := hdiff ρ C a b rr hρ hC F
  exact ⟨⟨ρ, C, a, b, rr, hρ, hC, F, R, hR, hRρ, η, h1, h2, h3, h4, h5⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- uniqueness of the canonical map on common domains (scaling with `s = 1`, `Phi_scale'`): the quadratic estimate transfers between any two unit-coupling settings. -/
theorem fderiv_Phi_quad_transfer (S0 S1 : Setting L 1 r one_pos) {C δ0 : ℝ} (hδ0 : δ0 ≤ S0.rM)
    (hq : ∀ v : L2T L, ‖v‖ < δ0 → ‖fderiv ℝ S0.Phi v - Setting.Fcl L‖ ≤ C * ‖v‖ ^ 2) {v : L2T L}
    (hv : ‖v‖ < min δ0 S1.rM) : ‖fderiv ℝ S1.Phi v - Setting.Fcl L‖ ≤ C * ‖v‖ ^ 2 := by
  have hmem : v ∈ ball (0 : L2T L) (min δ0 S1.rM) := mem_ball_zero_iff.2 hv
  have hev : S1.Phi =ᶠ[𝓝 v] S0.Phi := by
    filter_upwards [isOpen_ball.mem_nhds hmem] with w hw
    have hw' := mem_ball_zero_iff.1 hw
    have h := Setting.Phi_scale' S0 S1 one_pos (by norm_num : (1 : ℝ) = 1 * 1 ^ 2)
      (lt_of_lt_of_le hw' (min_le_right _ _)) (by rw [one_mul]; exact lt_of_lt_of_le hw' ((min_le_left _ _).trans hδ0))
    simpa using h.symm
  rw [hev.fderiv_eq]
  exact hq v (lt_of_lt_of_le hv (min_le_left _ _))

/-- **LOCAL-021 `prop:reset-moser-covariance`, repaired**: only the printed premises `L > 0`, `0 < r < 2π/L` and the printed full-analytic-diffeomorphism assumption on the exact-modulus family.
See the module docstring for the clause-by-clause correspondence. -/
theorem reset_moser_covariance_full {L r : ℝ} [Fact (0 < L)] (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (hdiff : FullDiffeoPremise L r) :
    -- (0) the preceding exact-modulus family exists at every coupling (LOCAL-020)
    (∀ (κ : ℝ) (hκ : 0 < κ), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)), Fam020 L κ r ρ C hκ a b rr) ∧
    -- (1) at every coupling and on every such family: a (constructed) setting with the printed conclusions
    (∀ (κ : ℝ) (hκ : 0 < κ) (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρ → 0 ≤ C → Fam020 L κ r ρ C hκ a b rr →
        ∃ S : Setting L κ r hκ, S.ρ = ρ ∧ S.C = C ∧ S.a = a ∧ S.b = b ∧ S.rr = rr ∧ SettingProps S) ∧
    -- (2) scaling between the (constructed) settings at couplings `κ` and `κ s²`
    (∀ (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
        (ρA CA : ℝ) (aA : ℤ → L2T L → ℝ) (bA : ℤ → L2T L → ℂ) (rrA : L2T L → (ℤ →ᵇ ℝ))
        (ρB CB : ℝ) (aB : ℤ → L2T L → ℝ) (bB : ℤ → L2T L → ℂ) (rrB : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρA → 0 ≤ CA → 0 < ρB → 0 ≤ CB → Fam020 L κ r ρA CA hκ aA bA rrA →
        Fam020 L (κ * s ^ 2) r ρB CB hκ₂ aB bB rrB →
        ∃ (SA : Setting L κ r hκ) (SB : Setting L (κ * s ^ 2) r hκ₂),
          SA.ρ = ρA ∧ SA.C = CA ∧ SA.a = aA ∧ SA.b = bA ∧ SA.rr = rrA ∧
          SB.ρ = ρB ∧ SB.C = CB ∧ SB.a = aB ∧ SB.b = bB ∧ SB.rr = rrB ∧ ScaleProps SA s hs hκ₂ SB) ∧
    -- (3) the constant `C_L`, the fixed unit-coupling chart, domains chosen by scaling, and the full fixed-ball estimate
    (∃ CL : ℝ, 0 ≤ CL ∧
      ∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρ → 0 ≤ C → Fam020 L 1 r ρ C one_pos a b rr →
        ∃ S1 : Setting L 1 r one_pos, S1.ρ = ρ ∧ S1.C = C ∧ S1.a = a ∧ S1.b = b ∧ S1.rr = rr ∧ SettingProps S1 ∧
          ∃ rs : ℝ, 0 < rs ∧ rs ≤ S1.rM ∧
            -- the chart at coupling `κ`: `Φ̂_κ(u) = κ^{-1/2} Φ_1(√κ u)` on `{√κ‖u‖ < rs}` agrees with the procedure's `Φ_κ` of every setting at coupling `κ`
            (∀ (κ : ℝ) (hκ : 0 < κ) (ρ' C' : ℝ) (a' : ℤ → L2T L → ℝ) (b' : ℤ → L2T L → ℂ) (rr' : L2T L → (ℤ →ᵇ ℝ)),
              0 < ρ' → 0 ≤ C' → Fam020 L κ r ρ' C' hκ a' b' rr' →
              ∃ S : Setting L κ r hκ, S.ρ = ρ' ∧ S.C = C' ∧ S.a = a' ∧ S.b = b' ∧ S.rr = rr' ∧ SettingProps S ∧
                ∀ u : L2T L, ‖u‖ < S.rM → Real.sqrt κ * ‖u‖ < rs → S.Phi u = PhiHat S1 κ u) ∧
            -- each fixed `L²` ball lies in the scaled domain for small `κ`, and there `‖DΦ̂_κ − 𝓕‖ ≤ C_L κ‖u‖²` (full `C¹` Fourier limit)
            (∀ ρ0 : ℝ, 0 < ρ0 → ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ0 → ∀ u : L2T L, ‖u‖ < ρ0 →
              Real.sqrt κ * ‖u‖ < rs ∧ DifferentiableAt ℝ (PhiHat S1 κ) u ∧
              ‖fderiv ℝ (PhiHat S1 κ) u - Setting.Fcl L‖ ≤ CL * κ * ‖u‖ ^ 2 ∧
              ‖PhiHat S1 κ u - Setting.Fcl L u‖ ≤ CL * κ * ‖u‖ ^ 3) ∧
            -- the printed scaling `Φ_κ(su) = sΦ_{κs²}(u)` on the scaled domains
            (∀ κ : ℝ, 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L, PhiHat S1 κ (s • u) = s • PhiHat S1 (κ * s ^ 2) u)) := by
  obtain ⟨Ch0⟩ := unit_chart hr hr2 hdiff
  refine ⟨fun κ hκ => fam020_exists hκ hr hr2, fun κ hκ ρ C a b rr hρ hC F => ?_, ?_, ?_⟩
  · obtain ⟨S, h1, h2, h3, h4, h5⟩ := (Chart.atCoupling Ch0 hκ hρ hC F).exists_setting
    exact ⟨S, h1, h2, h3, h4, h5, settingProps hr hr2 S⟩
  · intro κ hκ s hs hκ₂ ρA CA aA bA rrA ρB CB aB bB rrB hρA hCA hρB hCB FA FB
    obtain ⟨SA, a1, a2, a3, a4, a5⟩ := (Chart.atCoupling Ch0 hκ hρA hCA FA).exists_setting
    obtain ⟨SB, b1, b2, b3, b4, b5⟩ := (Chart.atCoupling Ch0 hκ₂ hρB hCB FB).exists_setting
    exact ⟨SA, SB, a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, scaleProps hr hr2 SA s hs hκ₂ SB⟩
  · obtain ⟨S0, -, -, -, -, -⟩ := Ch0.exists_setting
    obtain ⟨CL, δ0, hCL, hδ0, hδ0M, hq0⟩ := fderiv_Phi_quad S0
    refine ⟨CL, hCL, fun ρ C a b rr hρ hC F => ?_⟩
    obtain ⟨Ch1, c1, c2, c3, c4, c5⟩ := unit_chart_of_family hdiff hρ hC F
    obtain ⟨S1, g1, g2, g3, g4, g5⟩ := Ch1.exists_setting
    have hrs : 0 < min δ0 S1.rM := lt_min hδ0 S1.rM_pos
    have hrsM : min δ0 S1.rM ≤ S1.rM := min_le_right _ _
    have hq : ∀ v : L2T L, ‖v‖ < min δ0 S1.rM → ‖fderiv ℝ S1.Phi v - Setting.Fcl L‖ ≤ CL * ‖v‖ ^ 2 :=
      fun v hv => fderiv_Phi_quad_transfer S0 S1 hδ0M hq0 hv
    refine ⟨S1, g1.trans c1, g2.trans c2, g3.trans c3, g4.trans c4, g5.trans c5, settingProps hr hr2 S1,
      min δ0 S1.rM, hrs, hrsM, ?_, ?_, ?_⟩
    · intro κ hκ ρ' C' a' b' rr' hρ' hC' F'
      obtain ⟨S, h1, h2, h3, h4, h5⟩ := (Chart.atCoupling Ch1 hκ hρ' hC' F').exists_setting
      refine ⟨S, h1, h2, h3, h4, h5, settingProps hr hr2 S, fun u hu hsu => ?_⟩
      exact PhiHat_eq S1 S hu (lt_of_lt_of_le hsu hrsM)
    · intro ρ0 hρ0
      refine ⟨(min δ0 S1.rM / ρ0) ^ 2, by positivity, fun κ hκ hκ0 u hu => ?_⟩
      have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
      have hsu : Real.sqrt κ * ‖u‖ < min δ0 S1.rM := by
        have h1 : Real.sqrt κ < min δ0 S1.rM / ρ0 := (Real.sqrt_lt' (by positivity)).2 hκ0
        rw [lt_div_iff₀ hρ0] at h1
        calc Real.sqrt κ * ‖u‖ ≤ Real.sqrt κ * ρ0 := mul_le_mul_of_nonneg_left hu.le hs.le
          _ < min δ0 S1.rM := h1
      obtain ⟨hd, hb⟩ := PhiHat_deriv_bound S1 hrsM hq hκ hsu
      refine ⟨hsu, hd.differentiableAt, ?_, PhiHat_map_bound S1 hCL hrsM hq hκ hsu⟩
      rw [hd.fderiv]; exact hb
    · intro κ hκ s hs u
      exact PhiHat_scale S1 hκ hs u

end QuantumNLS.Local021Repair

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021Repair.unit_chart
#print axioms QuantumNLS.Local021Repair.unit_chart_of_family
#print axioms QuantumNLS.Local021Repair.fderiv_Phi_quad_transfer
#print axioms QuantumNLS.Local021Repair.reset_moser_covariance_full
