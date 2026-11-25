import Mathlib
import QuantumNLS.Local021Setting
import QuantumNLS.Local021Deriv
import QuantumNLS.Local021SetScale
import QuantumNLS.Local021SetPlane
import QuantumNLS.Local021ScaleAux

/-!
# LOCAL-021 `prop:reset-moser-covariance` (`local_covariance.tex:134`): the single named theorem `reset_moser_covariance`

Printed statement.  "Suppose the preceding exact-modulus family is a full analytic diffeomorphism between Hilbert balls.  The radial-primitive and scalar Haar
procedure in Theorem `thm:reset-moser` preserves all its stated covariances.  The resulting canonical map `Φ = S⁻¹ ∘ ζ` agrees with `𝓕` on every Fourier
plane, has `Φ_κ(su) = s Φ_{κ s²}(u)`, and has the Fourier derivative at zero.  With domains chosen by this scaling, on each fixed bounded `L²` ball
`‖DΦ_κ(u) - 𝓕‖ ≤ C_L κ ‖u‖₂²` for sufficiently small positive `κ`.  Thus the free limit is a full `C¹` Fourier limit on such balls."

Formalization (see `Local021Setting` for the data `Setting`):
* clause (0): the preceding family exists at every coupling (`fam020_exists`, from the frozen LOCAL-020);
* for every `Setting` (one coupling): (i) `S = MD.Sfl 1`, `S⁻¹ = MD.Tinv` are the LOCAL-017 outputs, and are the time-one flow of `Y_t` (`MoserFlowSpec`);
  (ii) for each of the six symmetries `U` (translation, boost, reflection, `star`, `C`, common phase): `U^*Ω = εΩ`, `β_{Uz}(Uh) = εβ_z(h)`, `f(Uz) = εf(z)`,
  `β⁰_{Uz}(Uh) = εβ⁰_z(h)`, `Y_t(Uz) = UY_t(z)`, `S(Uz) = US(z)`, `S⁻¹(Uz) = US⁻¹(z)`, `Φ(Tu) = UΦ(u)` (and the explicit index forms);
  (iii) `Φ(c e_k) = 𝓕(c e_k)`, `S` fixes every plane; (iv) `DΦ(0) = 𝓕`;
* scaling between two settings at couplings `κ` and `κ s²`: `Ω`, `β⁰`-primitive `f`, `Y_t`, `S`, `Φ`;
* the estimate `‖DΦ_κ(u) - 𝓕‖ ≤ C κ ‖u‖²` for `κ` small on every bounded ball (`C` from the unit-coupling setting).
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

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.LocalSpectral (pm)

variable {L κ r : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- the LOCAL-017 conclusions for the explicit outputs `(MD.Sfl 1, MD.Tinv)` of the procedure, together with the flow description. -/
theorem procedure_spec (P : PrintedHyp) (B : PrintedBounds P) :
    ∃ C : ℝ, MoserData.CorrectsWith P.Ω ((moserDataN P.toHyp B.toNative).R0 / 4)
        ((moserDataN P.toHyp B.toNative).Sfl 1) (moserDataN P.toHyp B.toNative).Tinv C ∧
      MoserFlowSpec P.moserY (moserDataN P.toHyp B.toNative).R0 ((moserDataN P.toHyp B.toNative).R0 / 4)
        ((moserDataN P.toHyp B.toNative).Sfl 1) (moserDataN P.toHyp B.toNative).Tinv := by
  set N := B.toNative with hN
  set MD := moserDataN P.toHyp N with hMD
  have hRle : MD.R0 ≤ P.R := (moserR0_le_R P.toHyp N).trans B.ρR
  have hballR : ball (0 : K) MD.R0 ⊆ ball (0 : K) P.R := ball_subset_ball hRle
  obtain ⟨C, hC⟩ := MD.sfl_corrects
  refine ⟨C, ?_, ?_⟩
  · obtain ⟨hC0, hmem, hinv, han, hanI, hpull, hq, h3, h2⟩ := hC
    refine ⟨hC0, hmem, hinv, han, hanI, ?_, hq, h3, h2⟩
    intro z hz a b
    have := hpull z hz a b
    have hS : MD.Sfl 1 z ∈ ball (0 : K) P.R :=
      hballR (ball_subset_ball (by linarith [MD.R0_pos]) ((hmem z hz).1))
    rwa [show P.toHyp.Ω (MD.Sfl 1 z) = P.Ω (MD.Sfl 1 z) from P.Om_eq hS] at this
  · have hY : ∀ t (u : K), u ∈ ball (0 : K) MD.R0 → P.moserY t u = MD.Yf t u :=
      fun t u hu => P.moserY_eq_Yf B t (hballR hu)
    refine ⟨fun t z => MD.Sfl t z, fun τ w => MD.Srev τ w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hzn := mem_ball_zero_iff.1 hz
      have hz' : ‖z‖ ≤ MD.R0 / 4 := hzn.le
      refine ⟨MD.Sfl_zero z, fun t ht => ?_, fun t => MD.norm_Sfl t z⟩
      have := MD.Sfl_deriv hz' t
      rw [sig_eq (s := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩] at this
      rw [hY t _ (by rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith [MD.R0_pos])]
      exact this
    · intro z _; rfl
    · intro z hz γ h0γ hc hd hm t ht
      have hzn := mem_ball_zero_iff.1 hz
      refine MD.flow_unique hzn h0γ hc (fun s hs => ?_) hm t ht
      rw [← hY s _ (hm s hs)]
      exact hd s hs
    · intro w hw
      have hwn := mem_ball_zero_iff.1 hw
      refine ⟨MD.Srev_zero w, fun τ hτ => ?_⟩
      have := MD.Srev_deriv hwn.le τ
      rw [sig_eq (s := 1 - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩] at this
      have hnorm : ‖MD.Srev τ w‖ = ‖w‖ := MD.norm_Fl (w, 1) (-τ)
      rw [hY _ _ (by rw [mem_ball_zero_iff, hnorm]; linarith [MD.R0_pos])]
      exact this
    · intro w _; rfl
    · intro w hw γ h1 hc hd hm
      have hwn := mem_ball_zero_iff.1 hw
      refine MD.flow_unique_back hwn h1 hc (fun s hs => ?_) hm
      rw [← hY s _ (hm s hs)]
      exact hd s hs

namespace Setting

variable (S : Setting L κ r hκ)

theorem Phi_cov (s : SymKind) {u : L2T L} (hu : ‖u‖ < S.rM) :
    S.Phi (s.phys L u) = (s.mono L).act (S.Phi u) := by
  have hρ : u ∈ ball (0 : L2T L) S.ρ := mem_ball_zero_iff.2 (lt_trans hu S.rM_lt_rho)
  unfold Phi
  rw [zetaK_cov S.fam s hρ]
  exact Si_cov S.B (s.mono L) (S.covΩ s) (by rw [norm_zetaK S.fam hρ]; exact hu)

theorem Phi_cov_index (u : L2T L) (hu : ‖u‖ < S.rM) (n : ℤ) :
    (∀ y : ℝ, S.Phi (QuantumNLS.BornTranslation.trans y u) n =
        Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * S.Phi u n) ∧
    (∀ k : ℤ, S.Phi (QuantumNLS.RootMassBoostSymbol.boost k u) n = S.Phi u (n - k)) ∧
    S.Phi (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = S.Phi u (-n) ∧
    S.Phi (star u) n = conj (S.Phi u (-n)) ∧
    (∀ φ : ℝ, S.Phi (Complex.exp ((φ : ℂ) * Complex.I) • u) n = Complex.exp ((φ : ℂ) * Complex.I) * S.Phi u n) ∧
    S.Phi (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = conj (S.Phi u n) := by
  refine ⟨fun y => ?_, fun k => ?_, ?_, ?_, fun φ => ?_, ?_⟩
  · have := congrArg (fun w : K => w n) (S.Phi_cov (SymKind.trans y) hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (S.Phi_cov (SymKind.boost k) hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj, sub_eq_add_neg] using this
  · have := congrArg (fun w : K => w n) (S.Phi_cov SymKind.refl hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (S.Phi_cov SymKind.cj hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (S.Phi_cov (SymKind.phase φ) hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (S.Phi_cov SymKind.cjr hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this


/-- scaling for settings whose couplings are related by an equation. -/
theorem Phi_scale' {κA κB : ℝ} {hA : 0 < κA} {hB : 0 < κB} (SA : Setting L κA r hA) (SB : Setting L κB r hB)
    {s : ℝ} (hs : 0 < s) (hκB : κB = κA * s ^ 2) {u : L2T L} (hu : ‖u‖ < SB.rM) (hsu : s * ‖u‖ < SA.rM) :
    SA.Phi ((s : ℂ) • u) = (s : ℂ) • SB.Phi u := by
  subst hκB
  exact SA.Phi_scale hs hB SB hu hsu

/-- the derivative of `Φ` is unchanged by the scaling. -/
theorem fderiv_Phi_scale {κA κB : ℝ} {hA : 0 < κA} {hB : 0 < κB} (SA : Setting L κA r hA)
    (SB : Setting L κB r hB) {s : ℝ} (hs : 0 < s) (hκB : κB = κA * s ^ 2) {u : L2T L} (hu : ‖u‖ < SB.rM)
    (hsu : s * ‖u‖ < SA.rM) : fderiv ℝ SB.Phi u = fderiv ℝ SA.Phi (s • u) := by
  have hm1 : ∀ᶠ w in 𝓝 u, ‖w‖ < SB.rM := (isOpen_lt continuous_norm continuous_const).mem_nhds hu
  have hm2 : ∀ᶠ w in 𝓝 u, s * ‖w‖ < SA.rM :=
    (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds hsu
  have hev : (fun w : L2T L => SA.Phi (s • w)) =ᶠ[𝓝 u] fun w => s • SB.Phi w := by
    filter_upwards [hm1, hm2] with w h1 h2
    have := Phi_scale' SA SB hs hκB h1 h2
    rw [Complex.coe_smul, Complex.coe_smul] at this
    exact this
  have h1 := fderiv_smul_scale (f := SA.Phi) (g := SB.Phi) (z := u) hs.ne' hs.ne' hev
  rw [inv_mul_cancel₀ hs.ne', one_smul] at h1
  exact h1.symm

end Setting

/-- **LOCAL-021 `prop:reset-moser-covariance`.**  See the module docstring for the correspondence with the printed statement. -/
theorem reset_moser_covariance {L r : ℝ} [Fact (0 < L)] (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    -- (0) the preceding exact-modulus family exists at every coupling (LOCAL-020)
    (∀ (κ : ℝ) (hκ : 0 < κ), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)), Fam020 L κ r ρ C hκ a b rr) ∧
    -- the procedure, its covariances, the plane normalization and the derivative at zero, for every setting
    (∀ (κ : ℝ) (hκ : 0 < κ) (S : Setting L κ r hκ),
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
      fderiv ℝ S.Phi 0 = Setting.Fcl L) ∧
    -- coupling scaling between the settings at `κ` and `κ s²`
    (∀ (κ : ℝ) (hκ : 0 < κ) (SA : Setting L κ r hκ) (s : ℝ) (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
        (SB : Setting L (κ * s ^ 2) r hκ₂),
      (∀ y ∈ ball (0 : K) SB.P.R, s • y ∈ ball (0 : K) SA.P.R → SA.P.Ω (s • y) = SB.P.Ω y) ∧
      (∀ z ∈ ball (0 : K) SB.P.R, s • z ∈ ball (0 : K) SA.P.R →
        QuantumNLS.LOCAL017Haar.primitive (betaR SA.P.toHyp) (s • z) =
          s ^ 2 * QuantumNLS.LOCAL017Haar.primitive (betaR SB.P.toHyp) z) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : K) SB.P.R, s • z ∈ ball (0 : K) SA.P.R →
        SA.P.moserY t (s • z) = s • SB.P.moserY t z) ∧
      (∀ z : K, ‖z‖ < SB.rM → s * ‖z‖ < SA.rM → SA.Sm (s • z) = s • SB.Sm z ∧ SA.Si (s • z) = s • SB.Si z) ∧
      (∀ u : L2T L, ‖u‖ < SB.rM → s * ‖u‖ < SA.rM → SA.Phi ((s : ℂ) • u) = (s : ℂ) • SB.Phi u)) ∧
    -- the quadratic estimate on every bounded `L²` ball for small `κ`, with the constant of the unit-coupling setting
    (∀ SA : Setting L 1 r one_pos, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ0 : ℝ, 0 < ρ0 → ∃ κ0 : ℝ, 0 < κ0 ∧
      ∀ (κ : ℝ) (hκ : 0 < κ), κ < κ0 → ∀ SB : Setting L κ r hκ, ∀ u : L2T L, ‖u‖ < ρ0 → ‖u‖ < SB.rM →
        ‖fderiv ℝ SB.Phi u - Setting.Fcl L‖ ≤ C * κ * ‖u‖ ^ 2) := by
  refine ⟨fun κ hκ => fam020_exists hκ hr hr2, fun κ hκ S => ?_, ?_, ?_⟩
  · refine ⟨procedure_spec S.P S.B, fun s => ?_, fun u hu n => S.Phi_cov_index u hu n, fun k c hc => S.Phi_plane k c hc,
      fun k z hz hzr => ⟨S.Sm_plane' hz hzr, S.Si_plane' hz hzr⟩, ?_⟩
    · exact ⟨S.covΩ s, fun z hz h => beta_cov S.P (s.mono L) (S.covΩ s) hz h,
        fun z hz => f_cov S.B (s.mono L) (S.covΩ s) hz, fun z hz h => beta0_cov S.B (s.mono L) (S.covΩ s) hz h,
        fun t ht z hz => moserY_cov S.B (s.mono L) (S.covΩ s) ht hz,
        fun z hz => ⟨Sm_cov S.B (s.mono L) (S.covΩ s) hz, Si_cov S.B (s.mono L) (S.covΩ s) hz⟩,
        fun u hu => S.Phi_cov s hu⟩
    · have h1 := S.fderiv_Phi 0
      rw [map_zero, S.fderiv_PhiK_zero] at h1
      exact h1
  · intro κ hκ SA s hs hκ₂ SB
    have hΩ := SA.scaleΩ_setting hs hκ₂ SB
    refine ⟨hΩ, fun z hz hsz => f_scale hs hΩ hz hsz, fun t ht z hz hsz => moserY_scale SA.B SB.B hs hΩ ht hz hsz,
      fun z hz hsz => ⟨Sm_scale SA.B SB.B hs hΩ hz hsz, Si_scale SA.B SB.B hs hΩ hz hsz⟩,
      fun u hu hsu => SA.Phi_scale hs hκ₂ SB hu hsu⟩
  · intro SA
    obtain ⟨C, δ, hC, hδ, hq⟩ := SA.PhiK_quad
    refine ⟨C, hC, fun ρ0 hρ0 => ?_⟩
    have hm : 0 < min δ SA.rM := lt_min hδ SA.rM_pos
    refine ⟨(min δ SA.rM / ρ0) ^ 2, by positivity, fun κ hκ hκ0 SB u hu hur => ?_⟩
    set s := Real.sqrt κ with hs
    have hspos : 0 < s := Real.sqrt_pos.2 hκ
    have hκs : κ = 1 * s ^ 2 := by rw [hs, Real.sq_sqrt hκ.le]; ring
    have hsρ : s * ρ0 < min δ SA.rM := by
      have h1 : s < min δ SA.rM / ρ0 := by
        rw [hs]
        exact (Real.sqrt_lt' (by positivity)).2 hκ0
      rwa [lt_div_iff₀ hρ0] at h1
    have hsu : s * ‖u‖ < min δ SA.rM := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hu.le hspos.le) hsρ
    have hsu' : s * ‖u‖ < SA.rM := lt_of_lt_of_le hsu (min_le_right _ _)
    have hd := Setting.fderiv_Phi_scale SA SB hspos hκs hur hsu'
    rw [hd, SA.fderiv_Phi]
    have hx : ‖fourierL2 L (s • u)‖ = s * ‖u‖ := by
      rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    have hq' := hq (fourierL2 L (s • u)) (by rw [hx]; exact lt_of_lt_of_le hsu (min_le_left _ _))
      (by rw [hx]; exact hsu')
    rw [hx] at hq'
    have e : (fderiv ℝ SA.PhiK (fourierL2 L (s • u))).comp (Setting.Fcl L) - Setting.Fcl L =
        (fderiv ℝ SA.PhiK (fourierL2 L (s • u)) - 1).comp (Setting.Fcl L) := by ext v; simp
    rw [e]
    calc ‖(fderiv ℝ SA.PhiK (fourierL2 L (s • u)) - 1).comp (Setting.Fcl L)‖
        ≤ ‖fderiv ℝ SA.PhiK (fourierL2 L (s • u)) - 1‖ * ‖Setting.Fcl L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (s * ‖u‖) ^ 2) * 1 := by gcongr; exact Setting.norm_Fcl_le
      _ = C * κ * ‖u‖ ^ 2 := by rw [hκs]; ring

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.procedure_spec
#print axioms QuantumNLS.Local021.reset_moser_covariance
