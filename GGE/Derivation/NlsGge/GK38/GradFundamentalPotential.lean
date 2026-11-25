import NlsGge.GK38.GradFundamentalDet

/-! # K1: independently defined potential resolvent variation.
GK Chapter I, Proposition 3.1. Differentiating the accepted Banach inverse is
connected below to the differentiated Volterra equation.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def potentialVolterraCLM38 (z : ℂ) : PotPair →L[ℂ] (PairCont38 →L[ℂ] PairCont38) :=
  (ContinuousLinearMap.compL ℂ PairCont38 PairCont38 PairCont38 (mulFree38 z)).comp
    (((ContinuousLinearMap.compL ℂ PairCont38 PairCont38 PairCont38).flip
      (mulFree38 z)).comp volterraZeroL)

@[simp] theorem potentialVolterraCLM38_apply (z : ℂ) (h : PotPair) :
    potentialVolterraCLM38 z h = volterraP h z := by
  exact (volterraP_eq_mul h z).symm

def fundPotentialResolventCLM38 (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] PairCont38 :=
  (Ring.inverse ((1 : PairCont38 →L[ℂ] PairCont38) - volterraP φ z)).comp
    ((ContinuousLinearMap.apply ℂ PairCont38 (fundContP φ z)).comp (potentialVolterraCLM38 z))

@[simp] theorem fundPotentialResolventCLM38_apply (φ : PotPair) (z : ℂ) (h : PotPair) :
    fundPotentialResolventCLM38 φ z h =
      Ring.inverse (1 - volterraP φ z) (volterraP h z (fundContP φ z)) := by
  simp [fundPotentialResolventCLM38]

theorem fundPotentialResolventCLM38_volterra (φ : PotPair) (z : ℂ) (h : PotPair) :
    fundPotentialResolventCLM38 φ z h = volterraP h z (fundContP φ z) +
      volterraP φ z (fundPotentialResolventCLM38 φ z h) := by
  have hc := congrArg (fun T : PairCont38 →L[ℂ] PairCont38 => T
    (volterraP h z (fundContP φ z)))
    (Ring.mul_inverse_cancel (1 - volterraP φ z) (isUnit_one_sub_volterraP φ z))
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply] at hc
  rw [fundPotentialResolventCLM38_apply]
  linear_combination hc

end
end NlsGge.GK38
