import Mathlib
import NlsGge.Atomic.G2.G2021
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.ProductRepr
import NlsGge.GK38.StdRootBranchesFactors

                                                                                                   
                                                                                                                   
                                                                                                    
                                                                                                                 
                                                                                                                                                    
                                                                                                                                       
                                                                                                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem rootFactor_sq_of_avoids (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hn : z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    rootFactor38 n (φ, z) ^ 2 =
      ((lamMinus φ n - z) * (lamPlus φ n - z)) / (Lib.piN n : ℂ) ^ 2 := by
  rw [rootFactor38, div_pow, tauN_value38 φ hφ n, gamma2_value38 φ hφ n]
  rw [add_comm (lamPlus φ n), stdRoot_sq38 _ _ _ hn]

theorem rootProduct_sq_identity (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hz : ∀ n : ℤ, n ≠ m → z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    perChar φ z =
      -4 * ((z - lamMinus φ m) * (z - lamPlus φ m)) * rootProduct m (φ, z) ^ 2 := by
  classical
  have hp : (φ, z) ∈ a5OmittedRootDomain38 m := ⟨hφ, hz⟩
  have hg : Multipliable (fun j => a5OmittedRootFactor38 m j (φ, z)) (symmetricIcc ℤ) :=
    a5OmittedRoot_multipliable38 m (φ, z) hp
  have hg2 : Multipliable (fun j => a5OmittedRootFactor38 m j (φ, z) ^ 2) (symmetricIcc ℤ) :=
    hg.pow 2
  set f : ℤ → ℂ := fun n => (lamPlus φ n - z) * (lamMinus φ n - z) / (Lib.piN n : ℂ) ^ 2 with hf
  have hupd : (fun x : ℤ => if x = m then (1 : ℂ) else f x) =
      fun j => a5OmittedRootFactor38 m j (φ, z) ^ 2 := by
    funext j
    by_cases hj : j = m
    · subst hj; simp [a5OmittedRootFactor38]
    · have e : a5OmittedRootFactor38 m j (φ, z) = rootFactor38 j (φ, z) := by
        simp [a5OmittedRootFactor38, hj]
      rw [if_neg hj, e, rootFactor_sq_of_avoids j φ hφ z (hz j hj)]
      simp only [hf]
      ring
  have hmu : Multipliable (fun x : ℤ => if x = m then (1 : ℂ) else f x) (symmetricIcc ℤ) := by
    rw [hupd]; exact hg2
  have hsplit : (∏'[symmetricIcc ℤ] n : ℤ, f n) =
      f m * ∏'[symmetricIcc ℤ] n : ℤ, (if n = m then (1 : ℂ) else f n) :=
    Multipliable.tprod_eq_mul_tprod_ite' m (by
      have e : Function.update f m 1 = fun x : ℤ => if x = m then (1 : ℂ) else f x := by
        funext x; simp [Function.update_apply]
      rw [e]; exact hmu)
  have hpow : (∏'[symmetricIcc ℤ] j : ℤ, a5OmittedRootFactor38 m j (φ, z) ^ 2) =
      a5OmittedRootProduct38 m (φ, z) ^ 2 := by
    rw [hg.tprod_pow 2]
    rfl
  rw [perChar_product φ z]
  change -4 * (∏'[symmetricIcc ℤ] n : ℤ, f n) = _
  rw [hsplit, hupd, hpow]
  unfold rootProduct f
  rw [mul_pow, inv_pow]
  have hpi : (Lib.piN m : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Lib.piN_ne_zero m)
  field_simp
  ring

end
end NlsGge.GKDefinitionDesign
