import NlsGge.GK38.GradEigenKernels

/-! K2 actual Dirichlet potential derivative before the simple-root quotient.
Private source anchor: GK I.7 Lemma 7.8; accepted K1 entry variations. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem dirichlet_characteristic_derivative (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ : PotPair => dirichletChar ψ z) (dirCLM φ z) φ := by
  have hd := (((hasFDerivAt_fundamentalEntryCLM38 φ z t1 1 0).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 1 1)).fun_sub
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 0 0)).fun_sub
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 0 1)
  have hscaled := hd.const_mul ((2 * Complex.I)⁻¹)
  simpa only [dirCLM, dirichletChar_eq, monodromyPair_eq_fundPair,
    t1, div_eq_mul_inv, mul_comm] using hscaled

end
end NlsGge.GK38.GradEigen38
