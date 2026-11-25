import Mathlib
import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.AbelianRatioCorrection
import NlsGge.GK38.Lib.EntireProductsParamd
import NlsGge.GK38.Lib.SymmPair
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.ThirdConsultation.G4.G4018Support3
/- H215_IDENT01 (proof development, AUTHOR; not self-reviewed). Pro round 9 section 10, step 4 (G4-018).
   Product identity: for (phi,z) in the omitted domain of the n-th index and ANY numerator sequence s,
   the actual ratio p2OmittedRatio38 n ((phi,s),z) is the convergent symmetric product over j of
   1 (j = n) and (sigmaOf s j - z)/stdRoot38 (tauN phi j) (gamma2 phi j) z (j != n).
   Route: both symmetric products are multipliable (Lib.multipliable_omit; a5OmittedRoot_multipliable38),
   the denominator is nonzero (a5OmittedRoot_ne_zero38), so the termwise quotient converges to the quotient of
   the limits (PRODRATIO01 lemma); the pi_n factors cancel termwise since pi_j != 0. No hypothesis beyond
   the domain membership. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open SummationFilter

namespace NlsGge.G4018Support

theorem p2OmittedRatio_hasProd (φ : PotPair) (n : ℤ) (s : Lib.L2Seq) (z : ℂ)
    (hp : (φ, z) ∈ a5OmittedRootDomain38 n) :
    HasProd (fun j : ℤ => if j = n then (1 : ℂ) else
        (Lib.sigmaOf s j - z) / stdRoot38 (tauN φ j) (gamma2 φ j) z)
      (p2OmittedRatio38 n ((φ, s), z)) (symmetricIcc ℤ) := by
  have hnum : Multipliable (fun j : ℤ => if j = n then (1 : ℂ) else
      (Lib.sigmaOf s j - z) / (Lib.piN j : ℂ)) (symmetricIcc ℤ) :=
    Lib.multipliable_omit n s z
  have hnumP : HasProd (fun j : ℤ => if j = n then (1 : ℂ) else
      (Lib.sigmaOf s j - z) / (Lib.piN j : ℂ))
      (∏'[symmetricIcc ℤ] j : ℤ, if j = n then (1 : ℂ) else
        (Lib.sigmaOf s j - z) / (Lib.piN j : ℂ)) (symmetricIcc ℤ) := hnum.hasProd
  have hden : Multipliable (fun j : ℤ => a5OmittedRootFactor38 n j (φ, z)) (symmetricIcc ℤ) :=
    a5OmittedRoot_multipliable38 n (φ, z) hp
  have hdenP : HasProd (fun j : ℤ => a5OmittedRootFactor38 n j (φ, z))
      (a5OmittedRootProduct38 n (φ, z)) (symmetricIcc ℤ) := hden.hasProd
  have hQ : a5OmittedRootProduct38 n (φ, z) ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, z) hp
  have hratio := hasProd_div_of_hasProd _ _ (symmetricIcc ℤ) _ _ hnumP hdenP hQ
  have hval : p2OmittedRatio38 n ((φ, s), z) =
      (∏'[symmetricIcc ℤ] j : ℤ, if j = n then (1 : ℂ) else
        (Lib.sigmaOf s j - z) / (Lib.piN j : ℂ)) / a5OmittedRootProduct38 n (φ, z) := by
    unfold p2OmittedRatio38
    rw [p2OmittedNumerator_product38]
  have hfun : (fun j : ℤ => if j = n then (1 : ℂ) else
      (Lib.sigmaOf s j - z) / stdRoot38 (tauN φ j) (gamma2 φ j) z) =
      fun j : ℤ => (if j = n then (1 : ℂ) else (Lib.sigmaOf s j - z) / (Lib.piN j : ℂ)) /
        a5OmittedRootFactor38 n j (φ, z) := by
    funext j
    by_cases hj : j = n
    · subst hj
      simp [a5OmittedRootFactor38]
    · have hπ : (Lib.piN j : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero j
      simp only [hj, if_false, a5OmittedRootFactor38, rootFactor38]
      rw [div_div_div_cancel_right₀ hπ]
  rw [hval, hfun]
  exact hratio

end NlsGge.G4018Support
