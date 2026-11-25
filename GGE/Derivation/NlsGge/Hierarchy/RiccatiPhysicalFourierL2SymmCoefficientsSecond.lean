import NlsGge.Analysis.H1Fourier

set_option autoImplicit false

/-! A minimal dictionary bridge for the actual Fourier isometry and its
inverse. This avoids unfolding semireducible definitions of `physicalFourier`
at a later H¹ derivative-class use site. -/

namespace NlsGge.Pilot

theorem physicalFourier_symm_apply
    (x : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    physicalFourier (physicalFourierL2.symm x) n = x n := by
  have hrepr := physicalFourierL2_apply (physicalFourierL2.symm x) n
  have hmap := congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => z n)
    (physicalFourierL2.apply_symm_apply x)
  exact hrepr.symm.trans hmap

end NlsGge.Pilot
