import Mathlib
import QuantumNLS.Local021RScale

/-!
# LOCAL-021 repair, stage R5: per-setting clause predicates, the scaled chart `Φ̂_κ`, and the full fixed-ball estimate

(The repaired headline `QuantumNLS.Local021Repair.reset_moser_covariance_full` is in `Local021RHeadline`.)

Printed statement (`local_covariance.tex:134`, `prop:reset-moser-covariance`).  "... With domains chosen by this scaling, on each fixed bounded `L²` ball `‖DΦ_κ(u) − 𝓕‖ ≤ C_L κ‖u‖₂²` for sufficiently small positive `κ`.
Thus the free limit is a full `C¹` Fourier limit on such balls."

* `FullDiffeoPremise L r` : the printed premise (the exact-modulus family is a full analytic diffeomorphism between Hilbert balls), at unit coupling;
* `SettingProps`, `ScaleProps` : the per-setting and scaling clauses of the frozen `Local021.reset_moser_covariance`, verbatim (`settingProps`, `scaleProps` are that theorem);
* `PhiHat S κ u = κ^{-1/2} Φ_1(√κ u)` : the canonical map at coupling `κ` on the scaled domain `{√κ‖u‖ < r_*}` (the ball of radius `r_*/√κ`);
  `PhiHat_eq` : it agrees with the procedure's `Φ_κ` of every setting at coupling `κ` on the common domain; `PhiHat_scale` : `Φ̂_κ(su) = sΦ̂_{κs²}(u)`;
* `PhiHat_deriv_bound`, `PhiHat_map_bound` : `‖DΦ̂_κ(u) − 𝓕‖ ≤ C κ‖u‖²` and `‖Φ̂_κ(u) − 𝓕u‖ ≤ C κ‖u‖³` whenever `√κ‖u‖ < δ` (`C, δ` of the unit chart only; the map bound integrates the derivative bound along the segment `[0,u]`).
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
open QuantumNLS.LocalSpectral (pm)

variable {L r : ℝ} [Fact (0 < L)]

/-- The printed premise "the preceding exact-modulus family is a full analytic diffeomorphism between Hilbert balls", at unit coupling:  for the LOCAL-020 family `(a, b, rr)` on its ball `ρ`, `ζ̃ = ζ ∘ 𝓕⁻¹ : ℓ² → ℓ²`
is real analytic on a ball `B_R` (`R ≤ ρ`) with real-analytic inverse `η` of `B_R` onto itself (`‖ζ̃ x‖ = ‖x‖`, so the image of `B_R` lies in `B_R`). -/
def FullDiffeoPremise (L r : ℝ) [Fact (0 < L)] : Prop :=
  ∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
    0 < ρ → 0 ≤ C → Fam020 L 1 r ρ C one_pos a b rr →
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ ∃ η : K → K,
      AnalyticOnNhd ℝ (zetaT L 1 b rr) (ball (0 : K) R) ∧ AnalyticOnNhd ℝ η (ball (0 : K) R) ∧
      (∀ y ∈ ball (0 : K) R, η y ∈ ball (0 : K) R) ∧
      (∀ y ∈ ball (0 : K) R, zetaT L 1 b rr (η y) = y) ∧ (∀ x ∈ ball (0 : K) R, η (zetaT L 1 b rr x) = x)

/-- The conclusions of the printed proposition for ONE setting (one coupling): the LOCAL-017 procedure outputs `S = MD.Sfl 1`, `S⁻¹ = MD.Tinv` (printed conclusions and the time-one flow of `Y_t`);
the covariances of `Ω`, radial primitive, Haar primitive, Moser field, `S`, `S⁻¹`, `Φ` under the six symmetries and their index forms; `Φ = 𝓕` on Fourier planes, `S` fixes planes; `DΦ(0) = 𝓕`.
(Verbatim the per-setting clause of the frozen `Local021.reset_moser_covariance`.) -/
def SettingProps {κ : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ) : Prop :=
      -- `S = MD.Sfl 1`, `S⁻¹ = MD.Tinv` are the outputs of the LOCAL-017 procedure: time-one flow of `Y_t`, with the printed conclusions
      (∃ C : ℝ, MoserData.CorrectsWith S.P.Ω S.rM S.Sm S.Si C ∧
        MoserFlowSpec S.P.moserY S.MD.R0 S.rM S.Sm S.Si) ∧
      -- covariances of the radial primitive, Haar primitive, Moser field, flow and of `Φ` under each of the six symmetries
      (∀ s : SymKind,
        (∀ y ∈ ball (0 : K) S.P.R, ∀ v w : K, S.P.Ω ((s.mono L).act y) ((s.mono L).act v) ((s.mono L).act w) =
          (s.mono L).eps * S.P.Ω y v w) ∧
        (∀ z ∈ ball (0 : K) S.P.R, ∀ h : K, betaR S.P.toHyp ((s.mono L).act z) ((s.mono L).act h) =
          (s.mono L).eps * betaR S.P.toHyp z h) ∧
        (∀ z ∈ ball (0 : K) S.B.radius, QuantumNLS.LOCAL017Haar.primitive (betaR S.P.toHyp) ((s.mono L).act z) =
          (s.mono L).eps * QuantumNLS.LOCAL017Haar.primitive (betaR S.P.toHyp) z) ∧
        (∀ z ∈ ball (0 : K) S.B.radius, ∀ h : K,
          QuantumNLS.LOCAL017Haar.beta0 (betaR S.P.toHyp) ((s.mono L).act z) ((s.mono L).act h) =
            (s.mono L).eps * QuantumNLS.LOCAL017Haar.beta0 (betaR S.P.toHyp) z h) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : K) S.B.radius,
          S.P.moserY t ((s.mono L).act z) = (s.mono L).act (S.P.moserY t z)) ∧
        (∀ z : K, ‖z‖ < S.rM → S.Sm ((s.mono L).act z) = (s.mono L).act (S.Sm z) ∧
          S.Si ((s.mono L).act z) = (s.mono L).act (S.Si z)) ∧
        (∀ u : L2T L, ‖u‖ < S.rM → S.Phi (s.phys L u) = (s.mono L).act (S.Phi u))) ∧
      -- the sequence actions of the report on `Φ`
      (∀ u : L2T L, ‖u‖ < S.rM → ∀ n : ℤ,
        (∀ y : ℝ, S.Phi (QuantumNLS.BornTranslation.trans y u) n =
          Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * S.Phi u n) ∧
        (∀ k : ℤ, S.Phi (QuantumNLS.RootMassBoostSymbol.boost k u) n = S.Phi u (n - k)) ∧
        S.Phi (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = S.Phi u (-n) ∧
        S.Phi (star u) n = conj (S.Phi u (-n)) ∧
        (∀ φ : ℝ, S.Phi (Complex.exp ((φ : ℂ) * Complex.I) • u) n = Complex.exp ((φ : ℂ) * Complex.I) * S.Phi u n) ∧
        S.Phi (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = conj (S.Phi u n)) ∧
      -- `Φ = 𝓕` on every Fourier plane, and `S` fixes every plane pointwise
      (∀ (k : ℤ) (c : ℂ), ‖c‖ < S.rM → S.Phi (c • modeLp L k) = fourierL2 L (c • modeLp L k)) ∧
      (∀ (k : ℤ) (z : K), z ∈ Plane k → ‖z‖ < S.rM → S.Sm z = z ∧ S.Si z = z) ∧
      -- the Fourier derivative at zero
      fderiv ℝ S.Phi 0 = Setting.Fcl L

/-- The scaling clauses between the settings at couplings `κ` and `κ s²` (verbatim the scaling clause of the frozen `Local021.reset_moser_covariance`). -/
def ScaleProps {κ : ℝ} {hκ : 0 < κ} (SA : Setting L κ r hκ) (s : ℝ) (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
    (SB : Setting L (κ * s ^ 2) r hκ₂) : Prop :=
      (∀ y ∈ ball (0 : K) SB.P.R, s • y ∈ ball (0 : K) SA.P.R → SA.P.Ω (s • y) = SB.P.Ω y) ∧
      (∀ z ∈ ball (0 : K) SB.P.R, s • z ∈ ball (0 : K) SA.P.R →
        QuantumNLS.LOCAL017Haar.primitive (betaR SA.P.toHyp) (s • z) =
          s ^ 2 * QuantumNLS.LOCAL017Haar.primitive (betaR SB.P.toHyp) z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : K) SB.P.R, s • z ∈ ball (0 : K) SA.P.R →
        SA.P.moserY t (s • z) = s • SB.P.moserY t z) ∧
      (∀ z : K, ‖z‖ < SB.rM → s * ‖z‖ < SA.rM → SA.Sm (s • z) = s • SB.Sm z ∧ SA.Si (s • z) = s • SB.Si z) ∧
      (∀ u : L2T L, ‖u‖ < SB.rM → s * ‖u‖ < SA.rM → SA.Phi ((s : ℂ) • u) = (s : ℂ) • SB.Phi u)

theorem settingProps (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {κ : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ) :
    SettingProps S := (reset_moser_covariance hr hr2).2.1 κ hκ S

theorem scaleProps (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {κ : ℝ} {hκ : 0 < κ} (SA : Setting L κ r hκ) (s : ℝ)
    (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2) (SB : Setting L (κ * s ^ 2) r hκ₂) : ScaleProps SA s hs hκ₂ SB :=
  (reset_moser_covariance hr hr2).2.2.1 κ hκ SA s hs hκ₂ SB

/-! ### The chart at coupling `κ` on the scaled domain, and the full fixed-ball estimate -/

theorem Phi_zero {κ : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ) : S.Phi 0 = 0 := by
  have := S.Phi_plane 0 0 (by simpa using S.rM_pos)
  simpa using this

theorem hasFDerivAt_Phi {κ : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ) {v : L2T L} (hv : ‖v‖ < S.rM) :
    HasFDerivAt S.Phi (fderiv ℝ S.Phi v) v := by
  have hx : ‖fourierL2 L v‖ < S.rM := by rwa [LinearIsometryEquiv.norm_map]
  have h1 := S.hasFDerivAt_PhiK hx
  have h2 : HasFDerivAt (Setting.Fcle L : L2T L → K) (Setting.Fcl L) v := (Setting.Fcle L).hasFDerivAt
  have h3 := h1.comp v h2
  have e : S.Phi = S.PhiK ∘ ⇑(Setting.Fcle L) := funext fun u => S.Phi_eq u
  have hd : DifferentiableAt ℝ S.Phi v := by rw [e]; exact h3.differentiableAt
  exact hd.hasFDerivAt

/-- the quadratic estimate for `DΦ` near the origin of `L²`, with a constant `C` and radius `δ ≤ rM`. -/
theorem fderiv_Phi_quad {κ : ℝ} {hκ : 0 < κ} (S : Setting L κ r hκ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ S.rM ∧
      ∀ v : L2T L, ‖v‖ < δ → ‖fderiv ℝ S.Phi v - Setting.Fcl L‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hq⟩ := S.PhiK_quad
  refine ⟨C, min δ S.rM, hC, lt_min hδ S.rM_pos, min_le_right _ _, fun v hv => ?_⟩
  have hx : ‖fourierL2 L v‖ = ‖v‖ := LinearIsometryEquiv.norm_map _ _
  have hq' := hq (fourierL2 L v) (by rw [hx]; exact lt_of_lt_of_le hv (min_le_left _ _))
    (by rw [hx]; exact lt_of_lt_of_le hv (min_le_right _ _))
  rw [hx] at hq'
  rw [S.fderiv_Phi]
  have e : (fderiv ℝ S.PhiK (fourierL2 L v)).comp (Setting.Fcl L) - Setting.Fcl L =
      (fderiv ℝ S.PhiK (fourierL2 L v) - 1).comp (Setting.Fcl L) := by ext w; simp
  rw [e]
  calc ‖(fderiv ℝ S.PhiK (fourierL2 L v) - 1).comp (Setting.Fcl L)‖
      ≤ ‖fderiv ℝ S.PhiK (fourierL2 L v) - 1‖ * ‖Setting.Fcl L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C * ‖v‖ ^ 2) * 1 := by gcongr; exact Setting.norm_Fcl_le
    _ = C * ‖v‖ ^ 2 := by ring

/-- The unit-coupling canonical map transported to coupling `κ` by the printed scaling `Φ̂_κ(u) = κ^{-1/2} Φ_1(√κ u)` (domain `√κ‖u‖ < r_M`, i.e. the ball of radius `r_M/√κ`). -/
def PhiHat (S : Setting L 1 r one_pos) (κ : ℝ) (u : L2T L) : K :=
  (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u)

theorem hasFDerivAt_PhiHat (S : Setting L 1 r one_pos) {s : ℝ} (hs : 0 < s) {u : L2T L} (hu : s * ‖u‖ < S.rM) :
    HasFDerivAt (fun w : L2T L => s⁻¹ • S.Phi (s • w)) (fderiv ℝ S.Phi (s • u)) u := by
  have hv : ‖s • u‖ < S.rM := by rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hP := hasFDerivAt_Phi S hv
  have hl : HasFDerivAt (fun w : L2T L => s • w) (s • ContinuousLinearMap.id ℝ (L2T L)) u :=
    (hasFDerivAt_id u).const_smul s
  have h := (hP.comp u hl).const_smul s⁻¹
  have e : s⁻¹ • ((fderiv ℝ S.Phi (s • u)).comp (s • ContinuousLinearMap.id ℝ (L2T L))) =
      fderiv ℝ S.Phi (s • u) := by
    ext w
    simp [smul_smul, inv_mul_cancel₀ hs.ne']
  exact h.congr_fderiv e

theorem PhiHat_deriv_bound (S : Setting L 1 r one_pos) {C δ : ℝ} (hδ : δ ≤ S.rM)
    (hq : ∀ v : L2T L, ‖v‖ < δ → ‖fderiv ℝ S.Phi v - Setting.Fcl L‖ ≤ C * ‖v‖ ^ 2)
    {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < δ) :
    HasFDerivAt (PhiHat S κ) (fderiv ℝ S.Phi (Real.sqrt κ • u)) u ∧
      ‖fderiv ℝ S.Phi (Real.sqrt κ • u) - Setting.Fcl L‖ ≤ C * κ * ‖u‖ ^ 2 := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  refine ⟨hasFDerivAt_PhiHat S hs (lt_of_lt_of_le hu hδ), ?_⟩
  have hv : ‖Real.sqrt κ • u‖ < δ := by rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have := hq _ hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, Real.sq_sqrt hκ.le] at this
  linarith

theorem PhiHat_map_bound (S : Setting L 1 r one_pos) {C δ : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ S.rM)
    (hq : ∀ v : L2T L, ‖v‖ < δ → ‖fderiv ℝ S.Phi v - Setting.Fcl L‖ ≤ C * ‖v‖ ^ 2)
    {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < δ) :
    ‖PhiHat S κ u - Setting.Fcl L u‖ ≤ C * κ * ‖u‖ ^ 3 := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set g : L2T L → K := fun w => PhiHat S κ w - Setting.Fcl L w with hg
  have hmem : ∀ w ∈ closedBall (0 : L2T L) ‖u‖, Real.sqrt κ * ‖w‖ < δ := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hw hs.le) hu
  have hder : ∀ w ∈ closedBall (0 : L2T L) ‖u‖,
      HasFDerivAt g (fderiv ℝ S.Phi (Real.sqrt κ • w) - Setting.Fcl L) w := by
    intro w hw
    exact (PhiHat_deriv_bound S hδ hq hκ (hmem w hw)).1.sub (Setting.Fcl L).hasFDerivAt
  have hbd : ∀ w ∈ closedBall (0 : L2T L) ‖u‖, ‖fderiv ℝ g w‖ ≤ C * κ * ‖u‖ ^ 2 := by
    intro w hw
    rw [(hder w hw).fderiv]
    refine (PhiHat_deriv_bound S hδ hq hκ (hmem w hw)).2.trans ?_
    have : ‖w‖ ≤ ‖u‖ := by rwa [mem_closedBall_zero_iff] at hw
    have h2 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [norm_nonneg w]
    have : 0 ≤ C * κ := mul_nonneg hC hκ.le
    nlinarith
  have h0 : g 0 = 0 := by
    simp only [hg, PhiHat, smul_zero, Phi_zero, map_zero, sub_zero]
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (𝕜 := ℝ) (s := closedBall (0 : L2T L) ‖u‖)
    (C := C * κ * ‖u‖ ^ 2) (fun w hw => (hder w hw).differentiableAt) hbd (convex_closedBall _ _)
    (mem_closedBall_self (norm_nonneg u)) (by rw [mem_closedBall_zero_iff])
  rw [h0, sub_zero, sub_zero] at this
  simpa [hg, pow_succ, mul_assoc, mul_comm, mul_left_comm] using this

theorem PhiHat_scale (S : Setting L 1 r one_pos) {κ : ℝ} (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (u : L2T L) :
    PhiHat S κ (s • u) = s • PhiHat S (κ * s ^ 2) u := by
  have h1 : Real.sqrt (κ * s ^ 2) = Real.sqrt κ * s := by
    rw [Real.sqrt_mul hκ.le, Real.sqrt_sq hs.le]
  have hk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  unfold PhiHat
  rw [h1, smul_smul, smul_smul]
  congr 1
  field_simp

theorem PhiHat_eq (S : Setting L 1 r one_pos) {κ : ℝ} {hκ : 0 < κ} (SB : Setting L κ r hκ) {u : L2T L}
    (hu : ‖u‖ < SB.rM) (hsu : Real.sqrt κ * ‖u‖ < S.rM) : SB.Phi u = PhiHat S κ u := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hκs : κ = 1 * Real.sqrt κ ^ 2 := by rw [Real.sq_sqrt hκ.le]; ring
  have h := Setting.Phi_scale' S SB hs hκs hu hsu
  have h' : S.Phi (Real.sqrt κ • u) = Real.sqrt κ • SB.Phi u := by
    have h2 := h
    rwa [Complex.coe_smul, Complex.coe_smul] at h2
  unfold PhiHat
  rw [h', smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

end QuantumNLS.Local021R

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021R.settingProps
#print axioms QuantumNLS.Local021R.scaleProps
#print axioms QuantumNLS.Local021R.fderiv_Phi_quad
#print axioms QuantumNLS.Local021R.PhiHat_deriv_bound
#print axioms QuantumNLS.Local021R.PhiHat_map_bound
#print axioms QuantumNLS.Local021R.PhiHat_scale
#print axioms QuantumNLS.Local021R.PhiHat_eq
