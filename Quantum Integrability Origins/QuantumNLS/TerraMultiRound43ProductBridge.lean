import QuantumNLS.TerraMultiRound39AlgebraBall
import QuantumNLS.RootH1RatioNonlinear
import QuantumNLS.RiccatiPointwiseRep

/-! Physical products in the Fourier model agree with the L²/L∞ product
used in the independent ratio construction. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
namespace QuantumNLS.TerraMultiRound43ProductBridge
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound39AlgebraBall
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioNonlinear

lemma fieldMap_product_ae (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (x y : Ell2) :
    fieldMap L a (by linarith : (0 : ℝ) ≤ a) (physicalProduct hLf.out ha x y) =ᵐ[volume]
      (fun z => fieldMap L a (by linarith : (0 : ℝ) ≤ a) x z *
        fieldMap L a (by linarith : (0 : ℝ) ≤ a) y z) := by
  obtain ⟨f, _, hfa, hfp, _⟩ := fieldMap_rep L ha x
  obtain ⟨g, _, hga, hgp, _⟩ := fieldMap_rep L ha y
  obtain ⟨h, _, hha, hhp, _⟩ := fieldMap_rep L ha (physicalProduct hLf.out ha x y)
  filter_upwards [hfa, hga, hha] with z hx hy hz
  rw [hz, hx, hy]
  have ht := physicalProduct_rep hLf.out ha x y (QuantumNLS.HaarResolvent.rep1 L z)
  unfold physRep at ht
  rw [← hhp, ← hfp, ← hgp] at ht
  simpa only [QuantumNLS.HaarResolvent.coe_rep1] using ht

/-- The model physical cubic equals the ratio-map cubic whenever the L∞
representative agrees almost everywhere with the model's physical field. -/
theorem fieldMap_cubic (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (u r : Ell2) (s : Linfty L)
    (hs : s =ᵐ[volume] fieldMap L a (by linarith : (0 : ℝ) ≤ a) r) :
    fieldMap L a (by linarith : (0 : ℝ) ≤ a)
      (physicalProduct hLf.out ha (jEll u) (physicalProduct hLf.out ha r r)) =
      cubic (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) s := by
  let U := fieldMap L a (by linarith : (0 : ℝ) ≤ a) u
  have hj : fieldMap L a (by linarith : (0 : ℝ) ≤ a) (jEll u) = star U := fieldMap_jEll L a _ u
  apply Lp.ext
  filter_upwards [fieldMap_product_ae L ha (jEll u) (physicalProduct hLf.out ha r r),
    fieldMap_product_ae L ha r r, coe_cubic U s, hs, Lp.coeFn_star U] with z h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, hj] 
  simp only [h5, Pi.star_apply, pow_two]

#print axioms fieldMap_product_ae
#print axioms fieldMap_cubic
end QuantumNLS.TerraMultiRound43ProductBridge
