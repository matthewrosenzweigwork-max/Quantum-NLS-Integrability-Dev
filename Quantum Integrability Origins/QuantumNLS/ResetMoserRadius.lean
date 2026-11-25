import QuantumNLS.ResetMoserFinal

/-!
# `thm:reset-moser` (LOCAL-017), radius dependence: `r` is an explicit function of the analytic operator bounds only

Source: `symplectic_correction.tex:25`: "Then, on a smaller ball `B_r` whose radius depends only on the analytic operator bounds for `Ω`, ...".
and the first paragraph of the proof: "Real analyticity at zero in the operator-valued sense gives a holomorphic extension to a ball in the complexification ...
Shrinking that ball gives uniform bounds for this series and its first two derivatives ... (eq:reset-moser-form-bounds)".

The *analytic operator bounds* of `Ω` are the datum `OperatorBounds S` (= the frozen sol_ext_b structure `LOCAL017SourceR19.NativeExtension S`): a radius `ρ` of the holomorphic extension,
the real constant `M` of `‖Ω_z − ω‖ ≤ M‖z‖²`, `‖DΩ_z‖ ≤ M‖z‖`, `‖D²Ω_z‖ ≤ M` on `B_ρ` (the bundle `Loc S ρ M`), the complex constant `C` with the cubic bound of the holomorphic radial primitive.
The previous `reset_moser` used the datum `nativeExtension S` chosen by `Classical.choice`.  Here the construction is redone for an ARBITRARY bound datum `N`, so that

* `moserRadius ρ M = min (ρ/2, 1/(2(M+1))) / 4` is a fixed explicit function of `(ρ, M)` (defined with no reference to `S`);
* `reset_moser_radius S N` : for EVERY bound datum `N : OperatorBounds S` the correction `S, S⁻¹` exists on `B_r` with `r = moserRadius N.radius N.realConstant`, with all the printed conclusions;
* `reset_moser_radius_exists`: `OperatorBounds S` is inhabited (`nativeExtension S`), so the old statement is recovered.

Only the constant `C` of the estimates may depend on more than `(ρ, M)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp QuantumNLS.LOCAL017SourceR19
  QuantumNLS.Ext025A4BanachComplexification

/-- The analytic operator bounds for `Ω`: radius `ρ` of the holomorphic extension, real constant `M` (eq:reset-moser-form-bounds on `B_ρ`), complex constant `C`. -/
abbrev OperatorBounds (S : Hyp) := NativeExtension S

/-- The radius of the Moser ball, as a function of the operator bounds `(ρ, M)` ALONE. -/
def moserRadius (ρ M : ℝ) : ℝ := min (ρ / 2) (1 / (2 * (M + 1))) / 4

/-- The inner (deformation) radius `R0 = min (ρ/2, 1/(2(M+1)))`; `moserRadius = R0 / 4`. -/
def moserR0 (ρ M : ℝ) : ℝ := min (ρ / 2) (1 / (2 * (M + 1)))

theorem moserRadius_eq (ρ M : ℝ) : moserRadius ρ M = moserR0 ρ M / 4 := rfl

section Gen

variable (S : Hyp) (N : OperatorBounds S)

def nativeDataN : LOCAL017Haar.ComplexData (E := CH) (betaR S) N.radius N.complexConstant :=
  LOCAL017Haar.canonicalData (betaR S) (radialBeta N.form) N.real_slice N.holomorphic N.cubic acceptedBridge

theorem itemTwoPotentialN : ∀ z ∈ ball (0 : K) N.radius, {n | z n ≠ 0}.Finite →
    Nonempty (LOCAL017Haar.OrbitPotential (betaR S) z) :=
  fun _ hz hfin => Hyp.orbitPot S N.loc hz hfin

theorem primitive_with_boundsN :
    AnalyticOnNhd ℝ (LOCAL017Haar.primitive (betaR S)) (ball 0 N.radius) ∧
    ContinuousOn (LOCAL017Haar.beta0 (betaR S)) (ball 0 N.radius) ∧
    (∀ z ∈ ball (0 : K) (N.radius / 2),
      |LOCAL017Haar.primitive (betaR S) z| ≤ N.realConstant * Real.pi * ‖z‖ ^ 4 ∧
      ‖fderiv ℝ (LOCAL017Haar.primitive (betaR S)) z‖ ≤ 64 * N.complexConstant * Real.pi * ‖z‖ ^ 3 ∧
      ‖iteratedFDeriv ℝ 2 (LOCAL017Haar.primitive (betaR S)) z‖ ≤ 576 * N.complexConstant * Real.pi * ‖z‖ ^ 2 ∧
      ‖LOCAL017Haar.beta0 (betaR S) z‖ ≤ (N.realConstant + 64 * N.complexConstant * Real.pi) * ‖z‖ ^ 3) ∧
    (∀ z ∈ ball (0 : K) N.radius, ∀ h ∈ Tz z, LOCAL017Haar.beta0 (betaR S) z h = 0) :=
  LOCAL017Haar.primitive_with_bounds (nativeDataN S N) N.loc.ρpos N.constant_nonneg
    (fun _ hz => (betaR_hasFDerivAt S N.loc hz).continuousAt.continuousWithinAt)
    (fun _ hz => norm_betaR_le S N.loc hz) (itemTwoPotentialN S N)

theorem betaR_analyticAtN {z : K} (hz : z ∈ ball (0 : K) N.radius) : AnalyticAt ℝ (betaR S) z := by
  have hAn : AnalyticOnNhd ℂ (radialBeta N.form) (ball (0 : CH) N.radius) :=
    GP05AcceptedBridgeR16.banachHolomorphicBridge _ _ isOpen_ball N.holomorphic
  have hzC : Cx.ι z ∈ ball (0 : CH) N.radius := by
    simpa [mem_ball_zero_iff, Cx.norm_ι] using hz
  have h1 : AnalyticAt ℝ (radialBeta N.form) (Cx.ι z) := (hAn _ hzC).restrictScalars
  have h2 : AnalyticAt ℝ (fun w : K => radialBeta N.form (Cx.ι w)) z :=
    h1.comp (Cx.ιL.analyticAt z)
  have h3 : AnalyticAt ℝ (fun w : K => reRestr (radialBeta N.form (Cx.ι w))) z :=
    (reRestr.analyticAt _).comp h2
  refine h3.congr ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  ext h
  rw [reRestr_apply, N.real_slice w hw h]
  simp

def bdBN : ℝ := 3 * N.realConstant + 640 * N.complexConstant * Real.pi

theorem moserR0_pos : 0 < moserR0 N.radius N.realConstant := by
  have := N.loc.ρpos
  have := N.loc.M0
  exact lt_min (by positivity) (by positivity)

theorem moserR0_le_half : moserR0 N.radius N.realConstant ≤ N.radius / 2 := min_le_left _ _

theorem moserR0_le_R : moserR0 N.radius N.realConstant ≤ N.radius :=
  (moserR0_le_half S N).trans (by have := N.loc.ρpos; linarith)

theorem moserMR : N.realConstant * moserR0 N.radius N.realConstant ^ 2 ≤ 1 / 4 := by
  have hM := N.loc.M0
  have h0 := moserR0_pos S N
  have h1 : moserR0 N.radius N.realConstant ≤ 1 / (2 * (N.realConstant + 1)) := min_le_right _ _
  have h2 : moserR0 N.radius N.realConstant * (2 * (N.realConstant + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * (N.realConstant + 1))).1 h1
  have h3 : (moserR0 N.radius N.realConstant * (2 * (N.realConstant + 1))) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    simpa using this
  nlinarith [sq_nonneg (N.realConstant - 1), sq_nonneg (moserR0 N.radius N.realConstant)]

theorem bdBN_nonneg : 0 ≤ bdBN S N := by
  have := N.loc.M0
  have := N.constant_nonneg
  unfold bdBN; positivity

theorem ball_sub_halfN : ball (0 : K) (moserR0 N.radius N.realConstant) ⊆ ball (0 : K) (N.radius / 2) :=
  ball_subset_ball (moserR0_le_half S N)

theorem ball_sub_RN : ball (0 : K) (moserR0 N.radius N.realConstant) ⊆ ball (0 : K) N.radius :=
  ball_subset_ball (moserR0_le_R S N)

theorem hLocN : Loc S (moserR0 N.radius N.realConstant) N.realConstant :=
  loc_mono N.loc (moserR0_pos S N) (moserR0_le_R S N)

theorem beta0_anN {z : K} (hz : z ∈ ball (0 : K) (moserR0 N.radius N.realConstant)) :
    AnalyticAt ℝ (LOCAL017Haar.beta0 (betaR S)) z := by
  have hzρ : z ∈ ball (0 : K) N.radius := ball_sub_RN S N hz
  obtain ⟨hAn, _, _, _⟩ := primitive_with_boundsN S N
  exact (betaR_analyticAtN S N hzρ).sub ((hAn z hzρ).fderiv)

theorem beta0_annN {z : K} (hz : z ∈ ball (0 : K) (moserR0 N.radius N.realConstant)) :
    ∀ h ∈ Tz z, LOCAL017Haar.beta0 (betaR S) z h = 0 := by
  obtain ⟨_, _, _, hann⟩ := primitive_with_boundsN S N
  exact hann z (ball_sub_RN S N hz)

theorem beta0_b3N {z : K} (hz : z ∈ ball (0 : K) (moserR0 N.radius N.realConstant)) :
    ‖LOCAL017Haar.beta0 (betaR S) z‖ ≤ bdBN S N * ‖z‖ ^ 3 := by
  obtain ⟨_, _, hbd, _⟩ := primitive_with_boundsN S N
  have h := (hbd z (ball_sub_halfN S N hz)).2.2.2
  refine h.trans ?_
  have hM := N.loc.M0
  have hC := N.constant_nonneg
  have : N.realConstant + 64 * N.complexConstant * Real.pi ≤ bdBN S N := by
    unfold bdBN
    have : 0 ≤ 640 * N.complexConstant * Real.pi - 64 * N.complexConstant * Real.pi := by
      have := Real.pi_pos; nlinarith
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem beta0_b2N {z : K} (hz : z ∈ ball (0 : K) (moserR0 N.radius N.realConstant)) :
    ‖fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z‖ ≤ bdBN S N * ‖z‖ ^ 2 := by
  have hdβ : ∀ z ∈ ball (0 : K) N.radius, DifferentiableAt ℝ (betaR S) z :=
    fun z hz => (betaR_hasFDerivAt S N.loc hz).differentiableAt
  have hb : ∀ z ∈ ball (0 : K) N.radius, ‖fderiv ℝ (betaR S) z‖ ≤ (2 * N.realConstant) * ‖z‖ ^ 2 :=
    fun z hz => norm_fderiv_betaR_le S N.loc hz
  obtain ⟨_, h⟩ := LOCAL017Haar.beta0_derivative_bound (nativeDataN S N) N.loc.ρpos
    N.constant_nonneg hdβ hb (ball_sub_halfN S N hz)
  refine h.trans ?_
  have hM := N.loc.M0
  have hC := N.constant_nonneg
  have : 2 * N.realConstant + 576 * N.complexConstant * Real.pi ≤ bdBN S N := by
    unfold bdBN
    have := Real.pi_pos
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem beta0_dN {z : K} (hz : z ∈ ball (0 : K) (moserR0 N.radius N.realConstant)) (a b : K) :
    fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z a b - fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z b a =
      (S.Ω z - omegaF) a b := by
  have hzρ : z ∈ ball (0 : K) N.radius := ball_sub_RN S N hz
  obtain ⟨hAn, _, _, _⟩ := primitive_with_boundsN S N
  have hβd : DifferentiableAt ℝ (betaR S) z :=
    (betaR_hasFDerivAt S N.loc hzρ).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ (LOCAL017Haar.primitive (betaR S))) z :=
    (hAn z hzρ).fderiv.differentiableAt
  have hsub : fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z =
      fderiv ℝ (betaR S) z - fderiv ℝ (fderiv ℝ (LOCAL017Haar.primitive (betaR S))) z :=
    fderiv_sub hβd hfd
  have hsym := ((hAn z hzρ).contDiffAt (n := (⊤ : WithTop ℕ∞))).isSymmSndFDerivAt_of_omega a b
  have hanti := betaR_antisym S N.loc hzρ a b
  rw [(betaR_hasFDerivAt S N.loc hzρ).fderiv] at hsub
  rw [hsub]
  have hDl : Dl S z a b = S.Ω z a b - omegaF a b := by simp [Dl]
  simp only [ContinuousLinearMap.sub_apply] at hanti ⊢
  rw [hDl] at hanti
  linarith [hsym, hanti]

/-- The Moser data on the ball of radius `moserR0 ρ M`, for an arbitrary operator-bound datum. -/
def moserDataN : MoserData S where
  R0 := moserR0 N.radius N.realConstant
  M := N.realConstant
  B := bdBN S N
  β0 := LOCAL017Haar.beta0 (betaR S)
  hL := hLocN S N
  hMR := moserMR S N
  B_nonneg := bdBN_nonneg S N
  β0_an := fun _ hz => beta0_anN S N hz
  β0_ann := fun _ hz => beta0_annN S N hz
  β0_b3 := fun _ hz => beta0_b3N S N hz
  β0_b2 := fun _ hz => beta0_b2N S N hz
  β0_d := fun _ hz a b => beta0_dN S N hz a b

end Gen

/-- `reset_moser` for an arbitrary Moser datum, `r = R0/4` (the body of `ResetMoserFinal.reset_moser`, with `moserData S` replaced by any `MD`). -/
theorem reset_moser_of_data (S : Hyp) (MD : MoserData S) :
    ∃ Sm Si : K → K, ∃ C : ℝ, 0 ≤ C ∧
      (∀ z ∈ ball (0 : K) (MD.R0 / 4), Sm z ∈ ball (0 : K) (MD.R0 / 4) ∧ Si z ∈ ball (0 : K) (MD.R0 / 4)) ∧
      (∀ z ∈ ball (0 : K) (MD.R0 / 4), Si (Sm z) = z ∧ Sm (Si z) = z) ∧
      AnalyticOnNhd ℝ Sm (ball (0 : K) (MD.R0 / 4)) ∧ AnalyticOnNhd ℝ Si (ball (0 : K) (MD.R0 / 4)) ∧
      (∀ z ∈ ball (0 : K) (MD.R0 / 4), ∀ a b : K,
        S.Ω (Sm z) (fderiv ℝ Sm z a) (fderiv ℝ Sm z b) = omegaF a b) ∧
      (∀ (n : ℤ), ∀ z ∈ ball (0 : K) (MD.R0 / 4), q n (Sm z) = q n z) ∧
      (∀ z ∈ ball (0 : K) (MD.R0 / 4), ‖Sm z - z‖ ≤ C * ‖z‖ ^ 3) ∧
      (∀ z ∈ ball (0 : K) (MD.R0 / 4), ‖fderiv ℝ Sm z - 1‖ + ‖fderiv ℝ Si z - 1‖ ≤ C * ‖z‖ ^ 2) := by
  have hR0 := MD.R0_pos
  obtain ⟨κ, hκ, hv⟩ := MD.exists_var_bound
  have hB := MD.B_nonneg
  refine ⟨MD.Sfl 1, MD.Tinv, MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2),
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    exact ⟨by rw [mem_ball_zero_iff, MD.norm_Sfl]; exact hn, by rw [mem_ball_zero_iff, MD.norm_Tinv]; exact hn⟩
  · intro z _
    exact ⟨MD.Tinv_Sfl_one z, MD.Sfl_one_Tinv z⟩
  · intro z hz
    exact MD.Sfl_one_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz
    exact MD.Tinv_analyticAt (mem_ball_zero_iff.1 hz)
  · intro z hz a b
    exact MD.pullback (mem_ball_zero_iff.1 hz) a b
  · intro n z _
    exact MD.q_Sfl n 1 z
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    refine (MD.norm_Sfl_sub_le hn).trans ?_
    have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have : MD.B ≤ MD.B + 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by
      have : 0 ≤ 2 * κ * Real.exp (κ * MD.R0 ^ 2) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this h3
  · intro z hz
    have hn := mem_ball_zero_iff.1 hz
    have hz2 : ‖z‖ ^ 2 ≤ MD.R0 ^ 2 := by
      have : ‖z‖ ≤ MD.R0 := by linarith
      nlinarith [norm_nonneg z]
    have hexp : Real.exp (κ * ‖z‖ ^ 2) ≤ Real.exp (κ * MD.R0 ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz2 hκ)
    have h1 : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 0) (by simpa using hn) 1 (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have h2 : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * ‖z‖ ^ 2) := by
      have := hv (z, 1) (by simpa using hn) (-1) (by simp) 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    have e1 : fderiv ℝ (MD.Sfl 1) z = Lam (fderiv ℝ (MD.Fl 1) (z, 0)) := MD.DS_eq 1 z
    have e2 : fderiv ℝ MD.Tinv z = Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) := (MD.hasFDerivAt_Tinv z).fderiv
    rw [e1, e2]
    have hk : 0 ≤ κ * ‖z‖ ^ 2 := by positivity
    have h1' : ‖Lam (fderiv ℝ (MD.Fl 1) (z, 0)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h1.trans (mul_le_mul_of_nonneg_left hexp hk)
    have h2' : ‖Lam (fderiv ℝ (MD.Fl (-1)) (z, 1)) - 1‖ ≤ κ * ‖z‖ ^ 2 * Real.exp (κ * MD.R0 ^ 2) :=
      h2.trans (mul_le_mul_of_nonneg_left hexp hk)
    have hBz : 0 ≤ MD.B * ‖z‖ ^ 2 := by positivity
    nlinarith [h1', h2', hBz]

/-- **`thm:reset-moser` with the radius an explicit function of the operator bounds.**  For every datum of analytic operator bounds `N` of `Ω`, the correction exists on
`B_r`, `r = moserRadius N.radius N.realConstant = min (ρ/2, 1/(2(M+1)))/4`, a function of `(ρ, M)` alone (`0 < r ≤ ρ/8 ≤ R`). -/
theorem reset_moser_radius (S : Hyp) (N : OperatorBounds S) :
    0 < moserRadius N.radius N.realConstant ∧ moserRadius N.radius N.realConstant ≤ S.R ∧
    ∃ Sm Si : K → K, ∃ C : ℝ, 0 ≤ C ∧
      (∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant),
        Sm z ∈ ball (0 : K) (moserRadius N.radius N.realConstant) ∧ Si z ∈ ball (0 : K) (moserRadius N.radius N.realConstant)) ∧
      (∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant), Si (Sm z) = z ∧ Sm (Si z) = z) ∧
      AnalyticOnNhd ℝ Sm (ball (0 : K) (moserRadius N.radius N.realConstant)) ∧
      AnalyticOnNhd ℝ Si (ball (0 : K) (moserRadius N.radius N.realConstant)) ∧
      (∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant), ∀ a b : K,
        S.Ω (Sm z) (fderiv ℝ Sm z a) (fderiv ℝ Sm z b) = omegaF a b) ∧
      (∀ (n : ℤ), ∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant), q n (Sm z) = q n z) ∧
      (∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant), ‖Sm z - z‖ ≤ C * ‖z‖ ^ 3) ∧
      (∀ z ∈ ball (0 : K) (moserRadius N.radius N.realConstant),
        ‖fderiv ℝ Sm z - 1‖ + ‖fderiv ℝ Si z - 1‖ ≤ C * ‖z‖ ^ 2) := by
  have h0 := moserR0_pos S N
  have hRle : moserR0 N.radius N.realConstant ≤ S.R := (moserR0_le_R S N).trans N.loc.ρR
  refine ⟨by rw [moserRadius_eq]; positivity, by rw [moserRadius_eq]; linarith, ?_⟩
  rw [moserRadius_eq]
  exact reset_moser_of_data S (moserDataN S N)

/-- Operator bounds exist for every `Hyp S`. -/
theorem operatorBounds_exists (S : Hyp) : Nonempty (OperatorBounds S) := exists_nativeExtension S

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.moserDataN
#print axioms QuantumNLS.ResetMoser.reset_moser_of_data
#print axioms QuantumNLS.ResetMoser.reset_moser_radius
#print axioms QuantumNLS.ResetMoser.operatorBounds_exists
