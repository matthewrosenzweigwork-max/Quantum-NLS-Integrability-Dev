import Mathlib
import NlsGge.Atomic.G6.G6032Sup1Core
import NlsGge.Atomic.G6.G6032Sup2Core
import NlsGge.Atomic.G6.G6033Core
import NlsGge.Atomic.G6.G6030Host
import NlsGge.Atomic.G6.G6029Core
import NlsGge.ThirdConsultation.G1.NormCalculus

/- G6032 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6032Core.lean,
   namespace NlsGge.ThirdConsultation.G6032S.  SUPPORT (no packet increment).
   G6032_of = the G6-032 head body (followup13 STATEMENTS/G6.md, verbatim) from hypotheses with EXACT producer types:
   hleft/hright = G6013 conjuncts 5/6, h21 = (G6021 ·).2, h29 = (G6029 ·).2.2, h30 = (G6030 · 1 ·).2.2,
   h31A = G6031.1, h31E = the energy-integral clause of G6031, hU / hEq = the realSlice-inclusion and k = 3 clauses of
   G2_045 3.  Route (G6032_STOP.md assembly, Pro r15 Q5 row G6-032):
   * trunc_iso: finite-gap truncations of an isospectral pair are isospectral (equal Birkhoff moduli on the window,
     zero outside; G6033S.iso_of_moduli);
   * ham_trace: for x in H², (H(recover x) : ℂ) = (4/3) Σ higherAction 3 (realSlice x) (G2-045 k=3, G6-031, and
     weakDerivative_star: w'·(w̄)' + w²w̄² = |w'|² + |w|⁴ a.e.);
   * ham_eq_smooth: equality for smooth isospectral data by higherAction_eq_of_isospectral (G6032Sup1Core);
   * G6032_of: H¹ limit of the truncations (G6-030, m = 1) and continuity of nlsHamiltonian (G6-031). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6032S
noncomputable section

theorem trunc_iso
    (hleft : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hright : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (h21 : ∀ u : PhysicalL2,
      Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)))
    (x y : PhysicalL2) (hiso : y ∈ isospectralSet x) (N : ℕ) :
    finiteGapTruncation N y ∈ isospectralSet (finiteGapTruncation N x) := by
  unfold finiteGapTruncation
  apply NlsGge.ThirdConsultation.G6033S.iso_of_moduli hleft hright h21
  intro n
  rw [G6029Aux.truncate_apply, G6029Aux.truncate_apply]
  split_ifs
  · have hx : physicalBirkhoff x ∈ physicalActionTorus (actionSequence x) := (h21 x).mapsTo (fun z => rfl)
    have hy : physicalBirkhoff y ∈ physicalActionTorus (actionSequence x) := (h21 x).mapsTo hiso
    rw [hx n, hy n]
  · rfl

theorem ham_trace
    (h31E : ∀ u : PhysicalSobolev38 ((1 : ℕ) : ℝ), nlsHamiltonian u = ∫ x,
      (‖weakDerivative (physicalSobolevEmbed 1 u) x‖^2 +
        ‖physicalSobolevEmbed 1 u x‖^4) ∂spatialMeasure)
    (U : Set PotPair)
    (hU : ∀ u : PhysicalL2, physicalSobolev ((3-1 : ℕ) : ℝ) u → realSlice u ∈ U)
    (hEq : ∀ φ ∈ U, (4/3 : ℂ) * (∑' n : ℤ, higherAction 3 φ n) =
      ∫ x : PhysicalCircle,
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2 ∂spatialMeasure)
    (x : PhysicalL2) (hx2 : fourierSeq38 x ∈ seqSobolev38 ((3-1 : ℕ) : ℝ))
    (hx1 : fourierSeq38 x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    ((nlsHamiltonian (physicalSobolevRecover 1 x) : ℝ) : ℂ) =
      (4/3 : ℂ) * ∑' n : ℤ, higherAction 3 (realSlice x) n := by
  have hφ := hU x ((physicalSobolev_iff_mem (3-1) x).2 hx2)
  rw [hEq _ hφ, h31E, (physicalSobolevEmbed_recover 1).2 x hx1, ← integral_complex_ofReal]
  apply integral_congr_ae
  have h1 := Lp.coeFn_star (weakDerivative x)
  have h2 := Lp.coeFn_star x
  filter_upwards [h1, h2] with t ht1 ht2
  simp only [realSlice_apply]
  rw [weakDerivative_star, ht1, ht2, Pi.star_apply, Pi.star_apply, Complex.star_def]
  have e1 := Complex.mul_conj' (weakDerivative x t)
  have e2 := Complex.mul_conj' (x t)
  rw [show (x t)^2 * (starRingEnd ℂ (x t))^2 = (x t * starRingEnd ℂ (x t))^2 by ring, e1, e2]
  push_cast
  ring

theorem ham_eq_smooth
    (h31E : ∀ u : PhysicalSobolev38 ((1 : ℕ) : ℝ), nlsHamiltonian u = ∫ x,
      (‖weakDerivative (physicalSobolevEmbed 1 u) x‖^2 +
        ‖physicalSobolevEmbed 1 u x‖^4) ∂spatialMeasure)
    (U : Set PotPair)
    (hU : ∀ u : PhysicalL2, physicalSobolev ((3-1 : ℕ) : ℝ) u → realSlice u ∈ U)
    (hEq : ∀ φ ∈ U, (4/3 : ℂ) * (∑' n : ℤ, higherAction 3 φ n) =
      ∫ x : PhysicalCircle,
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2 ∂spatialMeasure)
    (x y : PhysicalL2) (hiso : y ∈ isospectralSet x)
    (hx : ∀ k : ℕ, fourierSeq38 x ∈ seqSobolev38 (k : ℝ))
    (hy : ∀ k : ℕ, fourierSeq38 y ∈ seqSobolev38 (k : ℝ)) :
    nlsHamiltonian (physicalSobolevRecover 1 x) = nlsHamiltonian (physicalSobolevRecover 1 y) := by
  apply Complex.ofReal_injective
  rw [ham_trace h31E U hU hEq x (hx _) (hx 1), ham_trace h31E U hU hEq y (hy _) (hy 1),
    tsum_congr (fun n => higherAction_eq_of_isospectral 3 hiso n)]

theorem G6032_of
    (hleft : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hright : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (h21 : ∀ u : PhysicalL2,
      Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)))
    (h29 : ∀ (x : PhysicalL2) (N : ℕ), finiteGap (finiteGapTruncation N x) ∧
      ∀ k : ℕ, fourierSeq38 (finiteGapTruncation N x) ∈ seqSobolev38 (k : ℝ))
    (h30 : ∀ x : PhysicalL2, fourierSeq38 x ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      Tendsto (fun N : ℕ => finiteGapTruncationSobolev 1 N x) atTop
        (𝓝 (physicalSobolevRecover 1 x)))
    (h31A : AnalyticOnNhd ℝ nlsHamiltonian Set.univ)
    (h31E : ∀ u : PhysicalSobolev38 ((1 : ℕ) : ℝ), nlsHamiltonian u = ∫ x,
      (‖weakDerivative (physicalSobolevEmbed 1 u) x‖^2 +
        ‖physicalSobolevEmbed 1 u x‖^4) ∂spatialMeasure)
    (U : Set PotPair)
    (hU : ∀ u : PhysicalL2, physicalSobolev ((3-1 : ℕ) : ℝ) u → realSlice u ∈ U)
    (hEq : ∀ φ ∈ U, (4/3 : ℂ) * (∑' n : ℤ, higherAction 3 φ n) =
      ∫ x : PhysicalCircle,
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2 ∂spatialMeasure)
    (u v : PhysicalSobolev38 ((1 : ℕ) : ℝ))
    (hiso : physicalSobolevEmbed 1 v ∈ isospectralSet (physicalSobolevEmbed 1 u)) :
  nlsHamiltonian u = nlsHamiltonian v := by
  have hTu := h30 _ (physicalSobolevEmbed_mem 1 u)
  have hTv := h30 _ (physicalSobolevEmbed_mem 1 v)
  rw [(physicalSobolevEmbed_recover 1).1 u] at hTu
  rw [(physicalSobolevEmbed_recover 1).1 v] at hTv
  have hc : Continuous nlsHamiltonian := continuousOn_univ.1 h31A.continuousOn
  have lu := (hc.tendsto u).comp hTu
  have lv := (hc.tendsto v).comp hTv
  have heq : (nlsHamiltonian ∘ fun N : ℕ => finiteGapTruncationSobolev 1 N (physicalSobolevEmbed 1 u)) =
      (nlsHamiltonian ∘ fun N : ℕ => finiteGapTruncationSobolev 1 N (physicalSobolevEmbed 1 v)) := by
    funext N
    simp only [Function.comp, finiteGapTruncationSobolev]
    exact ham_eq_smooth h31E U hU hEq _ _ (trunc_iso hleft hright h21 _ _ hiso N) (h29 _ N).2 (h29 _ N).2
  rw [heq] at lu
  exact tendsto_nhds_unique lu lv

end
end NlsGge.ThirdConsultation.G6032S
