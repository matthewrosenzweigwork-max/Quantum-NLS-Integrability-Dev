import Mathlib
import NlsGge.ThirdConsultation.M.OddTraceGeneric
import NlsGge.Atomic.M.M014
import NlsGge.Atomic.M.M006
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.Spectral.ActualGapActionAllNE02_38

                                                                               
                                                                                                                   
                                                                                                                  
                                                                                        
                                                                                     
                                                                                  
                                                                                                  
                                                                        
                                                                                                               
                                                                                                                 
                                                                                                                  
                                                                                                   
                                                                                                                       
                                                                                                                     
                                                                                          
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.M

namespace NlsGge.ThirdConsultation.MTraceCore

/-- Odd higher actions are nonnegative (M-014 gap-height representation). -/
theorem higherAction_odd_nonneg (w : PhysicalL2) (n : ℤ) (m : ℕ) :
    0 ≤ higherAction w n (2 * m + 1) := by
  rw [(higher_action_gap_integral w n (2 * m + 1) (by omega)).2.2.2.2]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg ?_ (fun x _ => ?_))
  · unfold periodicMinus periodicPlus
    obtain ⟨⟨y, hy⟩, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 w n
    rw [hset] at hy
    exact hy.1.trans hy.2
  · rw [show 2 * m + 1 - 1 = 2 * m by omega]
    exact mul_nonneg ((even_two_mul m).pow_nonneg x) (actualGapHeightE02_38_nonneg w x)

theorem odd_trace_sobolev_of
    (hbridge : ∀ (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m)
      (φ : NlsGge.ThirdConsultation.KSPS.SobolevC (2 * m))
      (hpair : NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice (physicalOfSobolev u)),
      hierarchyCharge φ ⟨2 * m + 1, (by omega), (by omega)⟩ =
        (((-1 : ℝ) ^ (m + 1) * signedCharge m u : ℝ) : ℂ))
    (htrace : ∀ (N : ℕ) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
      (hreal : MRiccati.RealPair φ)
      (hfg : NlsGge.ThirdConsultation.finiteGap (MRiccati.realPhysicalFromPair φ))
      (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1),
      Summable (fun n : ℤ => higherAction (MRiccati.realPhysicalFromPair φ) n k) ∧
      (∑' n : ℤ, higherAction (MRiccati.realPhysicalFromPair φ) n k) =
        (-((2 * Complex.I) ^ (k - 1))⁻¹ *
          hierarchyCharge φ ⟨k, (by omega), hkN⟩).re)
    (hdense : ∀ (m : ℕ) (u : SobolevR m), ∃ v : ℕ → SobolevR m,
      Tendsto v atTop (𝓝 u) ∧ ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (physicalOfSobolev (v j)))
    (hlift : ∀ w : PhysicalL2, NlsGge.ThirdConsultation.finiteGap w → ∀ N : ℕ,
      ∃ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N,
        NlsGge.ThirdConsultation.KSPS.toPotPair φ = realSlice w)
    (hsumH : ∀ (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m),
      Summable (fun n : ℤ =>
        (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1)))
    (htailH : ∀ (m : ℕ) (hm : 1 ≤ m)
      (v : ℕ → SobolevR m) (u : SobolevR m)
      (hv : Tendsto v atTop (𝓝 u)),
      ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
        (∑' n : ℤ, if L ≤ n.natAbs then
          ENNReal.ofReal ((4 : ℝ) ^ m *
            higherAction (physicalOfSobolev (v j)) n (2 * m + 1))
          else 0) < ENNReal.ofReal ε)
    (hcontH : ∀ (n : ℤ) (k : ℕ) (hk : 1 ≤ k),
      Continuous (fun u : PhysicalL2 => higherAction u n k))
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    HasSum (fun n : ℤ =>
      (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1))
      (signedCharge m u) := by
  obtain ⟨v, hv, hfg⟩ := hdense m u
  set a : ℕ → ℤ → ℝ := fun j n =>
    (4 : ℝ) ^ m * higherAction (physicalOfSobolev (v j)) n (2 * m + 1) with ha
  set b : ℤ → ℝ := fun n =>
    (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1) with hb
  have ha0 : ∀ j n, 0 ≤ a j n := fun j n =>
    mul_nonneg (by positivity) (higherAction_odd_nonneg _ n m)
  have hb0 : ∀ n, 0 ≤ b n := fun n =>
    mul_nonneg (by positivity) (higherAction_odd_nonneg _ n m)
  -- the finite-gap trace for each approximant
  have hj : ∀ j : ℕ, Summable (a j) ∧ ∑' n : ℤ, a j n = signedCharge m (v j) := by
    intro j
    obtain ⟨φ, hφ⟩ := hlift (physicalOfSobolev (v j)) (hfg j) (2 * m)
    have hrp : MRiccati.realPhysicalFromPair φ = physicalOfSobolev (v j) := by
      unfold MRiccati.realPhysicalFromPair
      rw [hφ]
      rfl
    have hreal : MRiccati.RealPair φ := by
      unfold MRiccati.RealPair
      rw [hrp, hφ]
    obtain ⟨hS, hT⟩ := htrace (2 * m) φ hreal (by rw [hrp]; exact hfg j) (2 * m + 1) (by omega)
      (by omega)
    rw [hrp] at hS hT
    rw [show 2 * m + 1 - 1 = 2 * m by omega, hbridge m hm (v j) φ hφ,
      NlsGge.ThirdConsultation.MTraceGen.trace_sign] at hT
    refine ⟨hS.mul_left _, ?_⟩
    show ∑' n : ℤ, (4 : ℝ) ^ m * higherAction (physicalOfSobolev (v j)) n (2 * m + 1) = _
    rw [tsum_mul_left, hT]
    field_simp
  -- pointwise convergence
  have hPc : Continuous (fun w : SobolevR m => physicalOfSobolev w) :=
    (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)).continuous.comp
      (continuous_ordinarySobolevCoordinates m)
  have hpt : ∀ n : ℤ, Tendsto (fun j => a j n) atTop (𝓝 (b n)) := fun n =>
    ((((hcontH n (2 * m + 1) (by omega)).comp hPc).tendsto u).comp hv).const_mul _
  -- uniform tails (real form)
  have htail : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      ∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0) < ε := by
    intro ε hε
    obtain ⟨L, hL⟩ := htailH m hm v u hv ε hε
    exact ⟨L, fun j => NlsGge.ThirdConsultation.MTraceGen.ennreal_tail_to_real (a j) (ha0 j)
      (hj j).1 L ε hε (hL j)⟩
  have hbs : Summable b := hsumH m hm u
  have hlim := NlsGge.ThirdConsultation.MTraceGen.tendsto_tsum_of_uniform_tails a b ha0 hb0
    (fun j => (hj j).1) hbs hpt htail
  have hSc : Tendsto (fun j => signedCharge m (v j)) atTop (𝓝 (signedCharge m u)) :=
    ((continuous_signedCharge m).tendsto u).comp hv
  have heq : ∑' n : ℤ, b n = signedCharge m u :=
    tendsto_nhds_unique (hlim.congr (fun j => (hj j).2)) hSc
  rw [← heq]
  exact hbs.hasSum

end NlsGge.ThirdConsultation.MTraceCore
