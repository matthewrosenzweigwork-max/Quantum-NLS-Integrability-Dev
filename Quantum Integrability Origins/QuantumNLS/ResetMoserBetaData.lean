import QuantumNLS.ResetMoserBetaCone
import QuantumNLS.ResetMoserMoserData

/-!
# `thm:reset-moser` (LOCAL-017), items 3-4 joined: the covector `β⁰ = β − df` as `MoserData`

Source: `symplectic_correction.tex`, "A primitive in all angular directions, with full bounds": "Put `β⁰ = β − df`.  Thus `β⁰` annihilates `𝒯_z` at every `z`, `dβ⁰ = Ω − ω`, and its norm and
first derivative have orders three and two, respectively."

Everything here is the frozen read-only Haar stage (`LOCAL017SourceR19.nativeExtension`, `primitive_with_bounds`, `LOCAL017Haar.beta0_derivative_bound`; sol_ext_b) joined with this
role's frozen stages: `Hyp.orbitPot` (the item-2 finite-orbit potential, exactly the stage input `ItemTwoPotential`), `betaR_antisym` (`dβ = Ω − ω`), `betaR_analyticAt`, `norm_fderiv_betaR_le`.
There is **no extra hypothesis**: for every `Hyp S`,

* `itemTwoPotential S : ItemTwoPotential S` (the Haar stage input, discharged);
* `moserData S : MoserData S`, on the ball of radius `bdR0 S = min (ρ/2) (1/(2(M+1)))` (`ρ`, `M` from the native extension), with `β⁰ = LOCAL017Haar.beta0 (betaR S)`:
  analytic, annihilating `𝒯_z`, `‖β⁰‖ ≤ B‖z‖³`, `‖Dβ⁰‖ ≤ B‖z‖²`, `Dβ⁰(a)(b) − Dβ⁰(b)(a) = (Ω − ω)(a, b)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.LOCAL017SourceR19

theorem itemTwoPotential (S : Hyp) : ItemTwoPotential S :=
  fun _ hz hfin => Hyp.orbitPot S (nativeExtension S).loc hz hfin

section Consts

variable (S : Hyp)

def bdR : ℝ := (nativeExtension S).radius
def bdM : ℝ := (nativeExtension S).realConstant
def bdC : ℝ := (nativeExtension S).complexConstant
def bdR0 : ℝ := min (bdR S / 2) (1 / (2 * (bdM S + 1)))
def bdB : ℝ := 3 * bdM S + 640 * bdC S * Real.pi

theorem bdR_pos : 0 < bdR S := (nativeExtension S).loc.ρpos
theorem bdM_nonneg : 0 ≤ bdM S := (nativeExtension S).loc.M0
theorem bdC_nonneg : 0 ≤ bdC S := (nativeExtension S).constant_nonneg

theorem bdR0_pos : 0 < bdR0 S := by
  have := bdR_pos S
  have := bdM_nonneg S
  exact lt_min (by positivity) (by positivity)

theorem bdR0_le_half : bdR0 S ≤ bdR S / 2 := min_le_left _ _

theorem bdR0_le_R : bdR0 S ≤ bdR S := (bdR0_le_half S).trans (by have := bdR_pos S; linarith)

theorem bdMR : bdM S * bdR0 S ^ 2 ≤ 1 / 4 := by
  have hM := bdM_nonneg S
  have h0 := bdR0_pos S
  have h1 : bdR0 S ≤ 1 / (2 * (bdM S + 1)) := min_le_right _ _
  have h2 : bdR0 S * (2 * (bdM S + 1)) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * (bdM S + 1))).1 h1
    exact this
  have h3 : (bdR0 S * (2 * (bdM S + 1))) ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    simpa using this
  nlinarith [sq_nonneg (bdM S - 1), sq_nonneg (bdR0 S)]

theorem bdB_nonneg : 0 ≤ bdB S := by
  have := bdM_nonneg S
  have := bdC_nonneg S
  unfold bdB; positivity

theorem ball_sub_half : ball (0 : K) (bdR0 S) ⊆ ball (0 : K) (bdR S / 2) :=
  ball_subset_ball (bdR0_le_half S)

theorem ball_sub_R : ball (0 : K) (bdR0 S) ⊆ ball (0 : K) (bdR S) :=
  ball_subset_ball (bdR0_le_R S)

theorem hLoc : Loc S (bdR0 S) (bdM S) := loc_mono (nativeExtension S).loc (bdR0_pos S) (bdR0_le_R S)

theorem beta0_an {z : K} (hz : z ∈ ball (0 : K) (bdR0 S)) :
    AnalyticAt ℝ (LOCAL017Haar.beta0 (betaR S)) z := by
  have hzρ : z ∈ ball (0 : K) (nativeExtension S).radius := ball_sub_R S hz
  obtain ⟨hAn, _, _, _⟩ := primitive_with_bounds S (itemTwoPotential S)
  exact (betaR_analyticAt S hzρ).sub ((hAn z hzρ).fderiv)

theorem beta0_ann {z : K} (hz : z ∈ ball (0 : K) (bdR0 S)) :
    ∀ h ∈ Tz z, LOCAL017Haar.beta0 (betaR S) z h = 0 := by
  obtain ⟨_, _, _, hann⟩ := primitive_with_bounds S (itemTwoPotential S)
  exact hann z (ball_sub_R S hz)

theorem beta0_b3 {z : K} (hz : z ∈ ball (0 : K) (bdR0 S)) :
    ‖LOCAL017Haar.beta0 (betaR S) z‖ ≤ bdB S * ‖z‖ ^ 3 := by
  obtain ⟨_, _, hbd, _⟩ := primitive_with_bounds S (itemTwoPotential S)
  have h := (hbd z (ball_sub_half S hz)).2.2.2
  refine h.trans ?_
  have hM := bdM_nonneg S
  have hC := bdC_nonneg S
  have : bdM S + 64 * bdC S * Real.pi ≤ bdB S := by
    unfold bdB
    have : 0 ≤ 640 * bdC S * Real.pi - 64 * bdC S * Real.pi := by
      have := Real.pi_pos; nlinarith
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem beta0_b2 {z : K} (hz : z ∈ ball (0 : K) (bdR0 S)) :
    ‖fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z‖ ≤ bdB S * ‖z‖ ^ 2 := by
  have hdβ : ∀ z ∈ ball (0 : K) (nativeExtension S).radius, DifferentiableAt ℝ (betaR S) z :=
    fun z hz => (betaR_hasFDerivAt S (nativeExtension S).loc hz).differentiableAt
  have hb : ∀ z ∈ ball (0 : K) (nativeExtension S).radius,
      ‖fderiv ℝ (betaR S) z‖ ≤ (2 * bdM S) * ‖z‖ ^ 2 :=
    fun z hz => norm_fderiv_betaR_le S (nativeExtension S).loc hz
  obtain ⟨_, h⟩ := LOCAL017Haar.beta0_derivative_bound (nativeData S) (nativeExtension S).loc.ρpos
    (nativeExtension S).constant_nonneg hdβ hb (ball_sub_half S hz)
  refine h.trans ?_
  have hM := bdM_nonneg S
  have hC := bdC_nonneg S
  have : 2 * bdM S + 576 * bdC S * Real.pi ≤ bdB S := by
    unfold bdB
    have := Real.pi_pos
    nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem beta0_d {z : K} (hz : z ∈ ball (0 : K) (bdR0 S)) (a b : K) :
    fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z a b - fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z b a =
      (S.Ω z - omegaF) a b := by
  have hzρ : z ∈ ball (0 : K) (nativeExtension S).radius := ball_sub_R S hz
  obtain ⟨hAn, _, _, _⟩ := primitive_with_bounds S (itemTwoPotential S)
  have hβd : DifferentiableAt ℝ (betaR S) z :=
    (betaR_hasFDerivAt S (nativeExtension S).loc hzρ).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ (LOCAL017Haar.primitive (betaR S))) z :=
    (hAn z hzρ).fderiv.differentiableAt
  have hsub : fderiv ℝ (LOCAL017Haar.beta0 (betaR S)) z =
      fderiv ℝ (betaR S) z - fderiv ℝ (fderiv ℝ (LOCAL017Haar.primitive (betaR S))) z :=
    fderiv_sub hβd hfd
  have hsym := ((hAn z hzρ).contDiffAt (n := (⊤ : WithTop ℕ∞))).isSymmSndFDerivAt_of_omega a b
  have hanti := betaR_antisym S (nativeExtension S).loc hzρ a b
  rw [(betaR_hasFDerivAt S (nativeExtension S).loc hzρ).fderiv] at hsub
  rw [hsub]
  have hDl : Dl S z a b = S.Ω z a b - omegaF a b := by simp [Dl]
  simp only [ContinuousLinearMap.sub_apply] at hanti ⊢
  rw [hDl] at hanti
  linarith [hsym, hanti]

/-- The analytic data of the Moser deformation, for every `Hyp S`: no hypothesis beyond the printed ones. -/
def moserData : MoserData S where
  R0 := bdR0 S
  M := bdM S
  B := bdB S
  β0 := LOCAL017Haar.beta0 (betaR S)
  hL := hLoc S
  hMR := bdMR S
  B_nonneg := bdB_nonneg S
  β0_an := fun _ hz => beta0_an S hz
  β0_ann := fun _ hz => beta0_ann S hz
  β0_b3 := fun _ hz => beta0_b3 S hz
  β0_b2 := fun _ hz => beta0_b2 S hz
  β0_d := fun _ hz a b => beta0_d S hz a b

end Consts

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.itemTwoPotential
#print axioms QuantumNLS.ResetMoser.beta0_b2
#print axioms QuantumNLS.ResetMoser.beta0_d
#print axioms QuantumNLS.ResetMoser.moserData
