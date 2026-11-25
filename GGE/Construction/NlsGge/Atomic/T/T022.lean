                                                                                                                                                                                                                        
                                                                                                     
                                                                                                     
                                                                                         
                                                                                                    
                                                                                               
                                                                                                           
                                                                                     
                                                       
import Mathlib
import NlsGge.Birkhoff.SignedMoments38d
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.T
noncomputable section

def signedLocalChargeSobolev (r j : ℕ)
    (x : SobolevHilbert (r : ℝ)) : ℝ :=
  oddChargeSobolev38 (r + 1) j
    (show SobolevHilbert (((r + 1 - 1 : ℕ) : ℝ)) from by simpa using x)

private theorem t022_p_var_order (k : ℕ) (hk : 1 ≤ k) (m : Jet →₀ ℕ)
    (hm : m ∈ (p k).support) (v : Jet) (hv : v ∈ m.support) : v.2 < k := by
  obtain ⟨hw, hd, -⟩ := p_support_facts38 k hk m hm
  have hsum := weight_eq_deg_add38 m
  rw [hw] at hsum
  have hle : m v * v.2 ≤ m.sum (fun x e => e * x.2) := by
    unfold Finsupp.sum
    exact Finset.single_le_sum (f := fun x => m x * x.2) (fun x _ => Nat.zero_le _) hv
  have hm1 : 1 ≤ m v := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hv)
  have hv2 : v.2 ≤ m v * v.2 := le_mul_of_one_le_left (Nat.zero_le _) hm1
  linarith

private theorem t022_vars_order (j : ℕ) (a : Jet)
    (ha : a ∈ (formalOddChargeIntegrand38 j).vars) : a.2 < 2 * j + 2 := by
  unfold formalOddChargeIntegrand38 at ha
  have h1 := MvPolynomial.vars_mul
    (MvPolynomial.C ((-1 : ℤ) ^ (j + 1)) * (MvPolynomial.X ((false, 0) : Jet) : Poly))
    (p (2 * j + 2)) ha
  rcases Finset.mem_union.1 h1 with h | h
  · have h2 := MvPolynomial.vars_mul (MvPolynomial.C ((-1 : ℤ) ^ (j + 1)) : Poly)
      (MvPolynomial.X ((false, 0) : Jet) : Poly) h
    rcases Finset.mem_union.1 h2 with h3 | h3
    · rw [MvPolynomial.vars_C] at h3
      simp at h3
    · rw [MvPolynomial.vars_X] at h3
      rw [Finset.mem_singleton.1 h3]
      show 0 < 2 * j + 2
      omega
  · obtain ⟨d, hd, had⟩ := (MvPolynomial.mem_vars a).1 h
    exact t022_p_var_order (2 * j + 2) (by omega) d hd a had

theorem signedCharge_continuous_highSobolev (j : ℕ) :
    ∃ r : ℕ,
      r = 2 * j + 2 ∧
      (∀ q ∈ (formalOddChargeIntegrand38 j).support,
        ∀ a ∈ q.support, a.2 < r) ∧
      Continuous (signedLocalChargeSobolev r j) ∧
      (∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
        (hper : Function.Periodic U 1)
        (x : SobolevHilbert (r : ℝ)),
        (∀ n : ℤ,
          (show WeightedHilbert (sobolevModeWeight (r : ℝ)) from x) n =
            physicalFourier (smoothL2_38 U hU hper) n) →
        signedLocalChargeSobolev r j x = oddLocalCharge38 U j ∧
        oddLocalCharge38 U j =
          signedSpectralMoment38 (smoothL2_38 U hU hper) (2 * j + 1)) := by
  refine ⟨2 * j + 2, rfl, fun q hq a ha =>
    t022_vars_order j a ((MvPolynomial.mem_vars a).2 ⟨q, hq, ha⟩), ?_, ?_⟩
  · exact continuous_oddChargeSobolev38 (2 * j + 2 + 1) j (by omega)
  · intro U hU hper x hx
    exact ⟨oddChargeSobolev38_smooth (2 * j + 2 + 1) j (by omega) U hU hper x hx,
      ((signedSpectral_moments38 U hU hper (j + 1)).2 j (by omega)).symm⟩

end
end NlsGge.ThirdConsultation.T
