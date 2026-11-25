import NlsGge.GK38.PeriodicAsymptotics
import NlsGge.GK38.Lib.EntireProducts

/-! # S4: construction and exact orders of the spectral products

Source anchors: GK book I.6, Lemmas 6.5 and 6.8; Appendix C.
Square summability supplies symmetric convergence before product identities.
The combined periodic occurrence equality retains repeated roots.
-/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
namespace NlsGge.GK38
noncomputable section

def singleProduct38 (σ : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] m : ℤ, (σ m - z) / (πn m : ℂ)

def pairedFactors38 (φ : PotPair) (z : ℂ) (m : ℤ) : ℂ :=
  (lamPlus φ m - z) * (lamMinus φ m - z) / (πn m : ℂ) ^ 2

def pairedProduct38 (φ : PotPair) (z : ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] m : ℤ, pairedFactors38 φ z m

def periodicProduct38 (φ : PotPair) (z : ℂ) : ℂ := -4 * pairedProduct38 φ z

def criticalProduct38 (φ : PotPair) (z : ℂ) : ℂ := 2 * singleProduct38 (lamDot φ) z

theorem piN_complex_ne_zero38 (m : ℤ) : (πn m : ℂ) ≠ 0 := by
  exact_mod_cast Lib.piN_ne_zero m

theorem pairedFactors_eq_mul38 (φ : PotPair) (z : ℂ) (m : ℤ) :
    pairedFactors38 φ z m =
      ((lamPlus φ m - z) / (πn m : ℂ)) * ((lamMinus φ m - z) / (πn m : ℂ)) := by
  have hden := piN_complex_ne_zero38 m
  unfold pairedFactors38
  field_simp

theorem perChar_multipliable (φ : PotPair) (z : ℂ) :
    Multipliable (fun m : ℤ => (lamPlus φ m - z) * (lamMinus φ m - z) /
      (πn m : ℂ) ^ 2) (symmetricIcc ℤ) := by
  have hp := (Lib.product_entire (lamPlus φ) (periodic_plus_summable38 φ)).1 z
  have hm := (Lib.product_entire (lamMinus φ) (periodic_minus_summable38 φ)).1 z
  change Multipliable (pairedFactors38 φ z) (symmetricIcc ℤ)
  have he : pairedFactors38 φ z = fun m =>
      ((lamPlus φ m - z) / (πn m : ℂ)) * ((lamMinus φ m - z) / (πn m : ℂ)) :=
    funext (pairedFactors_eq_mul38 φ z)
  rw [he]
  exact hp.mul hm

theorem discrimDeriv_multipliable (φ : PotPair) (z : ℂ) :
    Multipliable (fun k : ℤ => (lamDot φ k - z) / (πn k : ℂ)) (symmetricIcc ℤ) :=
  (Lib.product_entire (lamDot φ) (critical_summable38 φ)).1 z

theorem pairedProduct_eq_mul38 (φ : PotPair) (z : ℂ) :
    pairedProduct38 φ z = singleProduct38 (lamPlus φ) z * singleProduct38 (lamMinus φ) z := by
  have hp := (Lib.product_entire (lamPlus φ) (periodic_plus_summable38 φ)).1 z
  have hm := (Lib.product_entire (lamMinus φ) (periodic_minus_summable38 φ)).1 z
  simpa only [pairedProduct38, singleProduct38, pairedFactors_eq_mul38] using hp.tprod_mul hm

theorem differentiable_singleProduct38 (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :
    Differentiable ℂ (singleProduct38 σ) := (Lib.product_entire σ hσ).2.1

theorem differentiable_periodicProduct38 (φ : PotPair) :
    Differentiable ℂ (periodicProduct38 φ) := by
  have hp := differentiable_singleProduct38 (lamPlus φ) (periodic_plus_summable38 φ)
  have hm := differentiable_singleProduct38 (lamMinus φ) (periodic_minus_summable38 φ)
  have he : periodicProduct38 φ = fun z =>
      (-4 : ℂ) * (singleProduct38 (lamPlus φ) z * singleProduct38 (lamMinus φ) z) :=
    funext (fun z => congrArg (fun v : ℂ => (-4 : ℂ) * v) (pairedProduct_eq_mul38 φ z))
  rw [he]
  exact (hp.mul hm).const_mul (-4)

theorem differentiable_criticalProduct38 (φ : PotPair) :
    Differentiable ℂ (criticalProduct38 φ) :=
  (differentiable_singleProduct38 (lamDot φ) (critical_summable38 φ)).const_mul 2

theorem analyticOrderAt_periodicProduct38 (φ : PotPair) (w : ℂ) :
    analyticOrderAt (periodicProduct38 φ) w = analyticOrderAt (perChar φ) w := by
  have hp := Lib.product_entire (lamPlus φ) (periodic_plus_summable38 φ)
  have hm := Lib.product_entire (lamMinus φ) (periodic_minus_summable38 φ)
  have hc : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  have he : periodicProduct38 φ = (fun _ : ℂ => (-4 : ℂ)) *
      (singleProduct38 (lamPlus φ) * singleProduct38 (lamMinus φ)) :=
    funext (fun z => congrArg (fun v : ℂ => (-4 : ℂ) * v) (pairedProduct_eq_mul38 φ z))
  have hap : AnalyticAt ℂ (singleProduct38 (lamPlus φ)) w := hp.2.1.analyticAt w
  have ham : AnalyticAt ℂ (singleProduct38 (lamMinus φ)) w := hm.2.1.analyticAt w
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (-4 : ℂ)) w := analyticAt_const
  rw [he, analyticOrderAt_mul hconst (hap.mul ham),
    hc, zero_add, analyticOrderAt_mul hap ham]
  change analyticOrderAt (singleProduct38 (lamPlus φ)) w +
    analyticOrderAt (singleProduct38 (lamMinus φ)) w = _
  unfold singleProduct38
  rw [hp.2.2 w, hm.2.2 w, add_comm]
  exact lamMinusPlus_occurrence38 φ w

theorem analyticOrderAt_criticalProduct38 (φ : PotPair) (w : ℂ) :
    analyticOrderAt (criticalProduct38 φ) w = analyticOrderAt (deriv (discrim φ)) w := by
  have hd := Lib.product_entire (lamDot φ) (critical_summable38 φ)
  have hc : analyticOrderAt (fun _ : ℂ => (2 : ℂ)) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  change analyticOrderAt ((fun _ : ℂ => (2 : ℂ)) * singleProduct38 (lamDot φ)) w = _
  have had : AnalyticAt ℂ (singleProduct38 (lamDot φ)) w := hd.2.1.analyticAt w
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) w := analyticAt_const
  rw [analyticOrderAt_mul hconst had, hc, zero_add]
  change analyticOrderAt (singleProduct38 (lamDot φ)) w = _
  unfold singleProduct38
  rw [hd.2.2 w]
  exact (lamDot_occurrence38 φ w).2

end
end NlsGge.GK38
