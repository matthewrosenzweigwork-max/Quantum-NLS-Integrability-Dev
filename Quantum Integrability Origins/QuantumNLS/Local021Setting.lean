import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Mono
import QuantumNLS.Local021Haar
import QuantumNLS.Local021Equiv
import QuantumNLS.Local021Scale
import QuantumNLS.Local021Plane
import QuantumNLS.Local021Zeta

/-!
# LOCAL-021, stage 8a: the setting of the proposition, and transport of the covariances / scaling / plane facts to the Moser form

The proposition (`local_covariance.tex:134`) assumes "the preceding exact-modulus family is a full analytic diffeomorphism between Hilbert balls" and
concerns "the radial-primitive and scalar Haar procedure in Theorem `thm:reset-moser`" applied to `Ω = (ζ^{-1})^*ω` (`local_transform.tex:105`).
`Setting` bundles exactly these data at one coupling `κ`:

* the LOCAL-020 family `(a, b, rr)` on a ball `ρ` (`Fam020`, the proved conclusion of LOCAL-020);
* the full analytic diffeomorphism: `ζ̃ = ζ ∘ 𝓕⁻¹ : K → K` is real analytic on `B_R` with real-analytic inverse `η` onto `B_R`;
* the printed hypotheses `P : PrintedHyp` of `thm:reset-moser` for the form `Ω = (ζ̃⁻¹)^*ω`  (`P.Ω_y(v,w) = ω(Dη_y v, Dη_y w)`), with analytic operator bounds `B`.

The procedure's outputs are the literal LOCAL-017 objects `S = MD.Sfl 1`, `S⁻¹ = MD.Tinv`, `MD = moserDataN P.toHyp B.toNative`, and `Φ = S⁻¹ ∘ ζ`.
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

variable {L κ r : ℝ} [Fact (0 < L)]

/-- `ζ̃ = ζ ∘ 𝓕⁻¹ : K → K`, the exact-modulus map in Fourier variables. -/
def zetaT (L κ : ℝ) [Fact (0 < L)] (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)) (x : K) : K :=
  zetaK L κ b rr ((fourierL2 L).symm x)

/-- The setting of LOCAL-021 at one coupling. -/
structure Setting (L κ r : ℝ) [Fact (0 < L)] (hκ : 0 < κ) where
  ρ : ℝ
  C : ℝ
  a : ℤ → L2T L → ℝ
  b : ℤ → L2T L → ℂ
  rr : L2T L → (ℤ →ᵇ ℝ)
  hρ : 0 < ρ
  hC : 0 ≤ C
  fam : Fam020 L κ r ρ C hκ a b rr
  R : ℝ
  hR : 0 < R
  hRρ : R ≤ ρ
  η : K → K
  zeta_an : AnalyticOnNhd ℝ (zetaT L κ b rr) (ball (0 : K) R)
  eta_an : AnalyticOnNhd ℝ η (ball (0 : K) R)
  eta_mem : ∀ y ∈ ball (0 : K) R, η y ∈ ball (0 : K) R
  zeta_eta : ∀ y ∈ ball (0 : K) R, zetaT L κ b rr (η y) = y
  eta_zeta : ∀ x ∈ ball (0 : K) R, η (zetaT L κ b rr x) = x
  P : PrintedHyp
  hPR : P.R = R
  hΩ : ∀ y ∈ ball (0 : K) R, ∀ v w : K, P.Ω y v w = omegaF (fderiv ℝ η y v) (fderiv ℝ η y w)
  B : PrintedBounds P

namespace Setting

variable {hκ : 0 < κ} (S : Setting L κ r hκ)

/-- `ζ̃` of the setting. -/
def zt : K → K := zetaT L κ S.b S.rr

/-- the LOCAL-017 data of the procedure. -/
def MD : MoserData S.P.toHyp := moserDataN S.P.toHyp S.B.toNative

/-- the Moser radius `r = R_0/4`. -/
def rM : ℝ := S.MD.R0 / 4

/-- `S` and `S⁻¹` of the procedure. -/
def Sm : K → K := S.MD.Sfl 1

def Si : K → K := S.MD.Tinv

/-- `Φ = S⁻¹ ∘ ζ` on `L²(𝕋_L)` (the canonical map; `ζ(u) ∈ ℓ²`). -/
def Phi (u : L2T L) : K := S.Si (zetaK L κ S.b S.rr u)

theorem R0_le : S.MD.R0 ≤ S.B.radius := moserR0_le_R S.P.toHyp S.B.toNative

theorem radius_le : S.B.radius ≤ S.R := S.hPR ▸ S.B.ρR

theorem rM_pos : 0 < S.rM := by unfold rM; have := S.MD.R0_pos; positivity

theorem rM_lt_R : S.rM < S.R := by
  have := S.R0_le; have := S.radius_le; have := S.MD.R0_pos; unfold rM; linarith

theorem rM_lt_rho : S.rM < S.ρ := lt_of_lt_of_le S.rM_lt_R S.hRρ

theorem R0_lt_R : S.MD.R0 / 4 < S.R := S.rM_lt_R

theorem zt_norm {x : K} (hx : x ∈ ball (0 : K) S.ρ) : ‖S.zt x‖ = ‖x‖ := by
  unfold zt zetaT
  have hu : (fourierL2 L).symm x ∈ ball (0 : L2T L) S.ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
  rw [norm_zetaK S.fam hu, LinearIsometryEquiv.norm_map]

theorem fourier_symm_act (s : SymKind) (x : K) :
    (fourierL2 L).symm ((s.mono L).act x) = s.phys L ((fourierL2 L).symm x) := by
  apply (fourierL2 L).injective
  rw [LinearIsometryEquiv.apply_symm_apply, SymKind.fourier_phys, LinearIsometryEquiv.apply_symm_apply]

theorem zt_cov (s : SymKind) {x : K} (hx : x ∈ ball (0 : K) S.ρ) :
    S.zt ((s.mono L).act x) = (s.mono L).act (S.zt x) := by
  unfold zt zetaT
  rw [fourier_symm_act]
  have hu : (fourierL2 L).symm x ∈ ball (0 : L2T L) S.ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hx
  exact zetaK_cov S.fam s hu

theorem eta_cov (s : SymKind) {y : K} (hy : y ∈ ball (0 : K) S.R) :
    S.η ((s.mono L).act y) = (s.mono L).act (S.η y) := by
  set U := s.mono L
  have hηy := S.eta_mem y hy
  have h1 : U.act (S.η y) ∈ ball (0 : K) S.R := U.mem_ball hηy
  have h2 : S.zt (U.act (S.η y)) = U.act y := by
    rw [S.zt_cov s (ball_subset_ball S.hRρ hηy)]
    have := S.zeta_eta y hy
    exact congrArg U.act this
  have := S.eta_zeta _ h1
  rw [show S.zt = zetaT L κ S.b S.rr from rfl] at h2
  rw [h2] at this
  exact this

theorem deta_cov (s : SymKind) {y : K} (hy : y ∈ ball (0 : K) S.R) (v : K) :
    fderiv ℝ S.η ((s.mono L).act y) ((s.mono L).act v) = (s.mono L).act (fderiv ℝ S.η y v) := by
  set U := s.mono L
  have hd : DifferentiableAt ℝ S.η y := (S.eta_an y hy).differentiableAt
  have hev : (S.η ∘ U.cle) =ᶠ[𝓝 y] (U.cle ∘ S.η) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with y' hy'
    exact S.eta_cov s hy'
  have h1 := hev.fderiv_eq (𝕜 := ℝ)
  rw [U.cle.comp_right_fderiv] at h1
  have h2 : HasFDerivAt (U.cle ∘ S.η) (U.cle.toContinuousLinearMap.comp (fderiv ℝ S.η y)) y :=
    U.cle.toContinuousLinearMap.hasFDerivAt.comp y hd.hasFDerivAt
  rw [h2.fderiv] at h1
  exact congrArg (fun T : K →L[ℝ] K => T v) h1

/-- `U^*Ω = εΩ`. -/
theorem covΩ (s : SymKind) : CovΩ S.P (s.mono L) := by
  intro y hy v w
  set U := s.mono L
  have hyR : y ∈ ball (0 : K) S.R := S.hPR ▸ hy
  have hUy : U.act y ∈ ball (0 : K) S.R := U.mem_ball hyR
  rw [S.hΩ _ hUy, S.hΩ _ hyR, S.deta_cov s hyR, S.deta_cov s hyR, omegaF_apply, omegaF_apply, Mono.omega_act]

end Setting

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.Setting.covΩ
#print axioms QuantumNLS.Local021.Setting.deta_cov
#print axioms QuantumNLS.Local021.Setting.zt_norm
