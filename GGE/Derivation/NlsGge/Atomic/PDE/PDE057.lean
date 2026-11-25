import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Field
import NlsGge.ThirdConsultation.PDE.Round14QuarticBridge
import NlsGge.ThirdConsultation.G6.Round5
import NlsGge.Atomic.PDE.PDE027

/- PDE-057 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/PDE/PDE057.lean.
   Head verbatim from Pro round 14 (### PDE-057), with the lexical repair of dropping the unavailable
   `open NlsGge.SpectralFoundations NlsGge.GK38` (as for PDE-044).
   Route: nlsHamiltonian = hamH1 o Fourier (quartic_circle_eq), landed hamiltonian_derivative (PDE027) chain rule through the
   Fourier isometry, stdSymplectic38_fourierSeq38 and nlsVectorField_coefficient (Round14Field). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
namespace NlsGge.ThirdConsultation.PDE

theorem nlsHamiltonian_eq_hamH1 (q : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    NlsGge.GKDefinitionDesign.nlsHamiltonian q =
      hamH1 (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) q) := by
  have hc : fourierSeq38 (physicalSobolevEmbed 1 q) =
      carrierCoe38 ((1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) q) :=
    funext (physicalSobolevEmbed_fourier 1 q)
  unfold NlsGge.GKDefinitionDesign.nlsHamiltonian hamH1 ham
  rw [quartic_circle_eq q, hc]
  rfl

theorem actual_nls_hamiltonian_normalization
    (u : PhysicalSobolev38 ((3 : ℕ) : ℝ))
    (v : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
  omegaPhys38 (physicalSobolevEmbed 1 (nlsVectorField u))
      (physicalSobolevEmbed 1 v) =
    fderiv ℝ (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) (physicalCoreBase u) v := by
  set x : HamiltonianCore38 := physicalCoreFourier u with hx
  set E := physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) with hE
  have hfun : (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) =>
      NlsGge.GKDefinitionDesign.nlsHamiltonian q / 2) =
      fun q => (1 / 2 : ℝ) * hamH1 (E q) := by
    funext q
    rw [nlsHamiltonian_eq_hamH1]; ring
  have hb : E (physicalCoreBase u) = hamiltonianBase x := by
    simp [physicalCoreBase, hE, hx]
  have h1 : HasFDerivAt hamH1 (hamiltonianDifferential x) (E (physicalCoreBase u)) := by
    rw [hb]; exact hamiltonian_derivative x
  have h2 := (h1.const_mul (1 / 2 : ℝ))
  have h3 : HasFDerivAt (fun q : PhysicalSobolev38 ((1 : ℕ) : ℝ) => (1 / 2 : ℝ) * hamH1 (E q))
      (((1 / 2 : ℝ) • hamiltonianDifferential x).comp
        (E.toContinuousLinearEquiv : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] _))
      (physicalCoreBase u) :=
    h2.comp (physicalCoreBase u) E.toContinuousLinearEquiv.hasFDerivAt
  rw [hfun, h3.fderiv]
  -- coordinates
  set c3 := fourierSeq38 (physicalSobolevEmbed 3 u) with hc3
  have hcx : ∀ k : ℤ, carrierCoe38 (((1 : ℕ) : ℝ) + 2) x k = c3 k := fun k => by
    rw [hx, hc3, carrierCoe38_physicalCoreFourier, physicalSobolevEmbed_fourier]
  have hw : ∀ k : ℤ, fourierSeq38 (physicalSobolevEmbed 1 v) k =
      carrierCoe38 ((1 : ℕ) : ℝ) (E v) k := physicalSobolevEmbed_fourier 1 v
  set g : ℤ → ℂ := fun k => ((disp k : ℝ) : ℂ) * c3 k + nonlin c3 k with hg
  set w : ℤ → ℂ := carrierCoe38 ((1 : ℕ) : ℝ) (E v) with hwdef
  have hGcoord : ∀ k : ℤ, carrierCoe38 ((0 : ℕ) : ℝ) (hamiltonianGradient0 x) k = g k := by
    intro k
    rw [hamiltonianGradient0_coordinate, hg]
    have : carrierCoe38 (((1 : ℕ) : ℝ) + 2) x = c3 := funext hcx
    simp only [this]
  have hwcoord : ∀ k : ℤ, carrierCoe38 ((0 : ℕ) : ℝ) (incl01 (E v)) k = w k :=
    fun k => by rw [coe_incl01]
  have hsq : ∀ a : H0C38, Summable fun k : ℤ => ‖carrierCoe38 ((0 : ℕ) : ℝ) a k‖ ^ 2 := by
    intro a
    refine (carrier_hasSum_norm_sq38 ((0 : ℕ) : ℝ) a).summable.congr (fun k => ?_)
    rw [sobolevModeWeight_natCast_zero, one_mul]
  have hsum : Summable fun k : ℤ => (starRingEnd ℂ) (g k) * w k := by
    have := summable_conj_mul38 (hsq (hamiltonianGradient0 x)) (hsq (incl01 (E v)))
    simpa only [hGcoord, hwcoord] using this
  -- left side
  rw [← stdSymplectic38_fourierSeq38]
  unfold stdSymplectic38
  have key : ∀ z y : ℂ, ((starRingEnd ℂ) (-Complex.I * z) * y).im = ((starRingEnd ℂ) z * y).re := by
    intro z y
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hterm : ∀ k : ℤ,
      ((starRingEnd ℂ) (fourierSeq38 (physicalSobolevEmbed 1 (nlsVectorField u)) k) *
        fourierSeq38 (physicalSobolevEmbed 1 v) k).im =
      ((starRingEnd ℂ) (g k) * w k).re := by
    intro k
    rw [nlsVectorField_coefficient, hw]
    exact key (g k) (w k)
  rw [tsum_congr hterm, ← Complex.re_tsum hsum]
  -- right side
  have hd := hamiltonianDifferential_apply x (E v)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, smul_eq_mul]
  change _ = (1 / 2 : ℝ) * hamiltonianDifferential x (E v)
  rw [hd]
  have h' : carrierCoe38 (((1 : ℕ) : ℝ) + 2) x = c3 := funext hcx
  rw [h']
  rw [show (∑' k : ℤ, star (g k) * w k) = ∑' k : ℤ, (starRingEnd ℂ) (g k) * w k from rfl]
  ring

end NlsGge.ThirdConsultation.PDE
