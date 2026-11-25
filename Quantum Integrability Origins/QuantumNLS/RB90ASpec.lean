import QuantumNLS.Q07BUniformCutsR16
/-! integrator-authored trusted spec for R-B90ACAE9 lem:Q07Buniformcuts (Terra r174 FULL ACCEPT): headline statement(s) copied verbatim from Q07BUniformCutsR16 (QuantumNLS.Q07BUniformCutsR16). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.RB90ASpec
open QuantumNLS.Q07BUniformCutsR16
open PhysicalTensor (L2T)
open Q07IntegratedHessiansR16 (windowContour)
open Q07SobolevCutsR16 (sobolevClass)
open PROP017UniformN (cutSeq)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem q07Buniformcuts_spec (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) (r : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in cocompact ℝ,
      ∀ u ∈ sobolevClass (L := L) s B, ∀ y : ℝ, |y| ≤ h →
        ‖NormalizedTransfer.productSymbol L κ u (Q07StripInteractionR16.spectral t y)-1-
          Complex.exp (Complex.I*Q07StripInteractionR16.spectral t y*L)‖ < ε) ∧
    ∃ η : ℝ, 0 < η ∧ ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧
        ∀ u ∈ sobolevClass (L := L) s B, ∀ v : L2T L, ‖v-u‖ < η →
          (∀ a : ℝ, (a = cutSeq L l ∨ a = -cutSeq L l) →
            (∀ t : ℝ, |t| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) v (a+t)| < 3/2) ∧
            FullMass.Mmeas κ v (Ioo (a-1/L) (a+1/L)) = 0) ∧
          windowContour hκ r (cutSeq L l) h v =
            (∫ t in Ioo (-cutSeq L l) (cutSeq L l), t^r ∂FullMass.Mmeas κ v) ∧
          DifferentiableAt ℝ (windowContour hκ r (cutSeq L l) h) v ∧
          DifferentiableAt ℝ (fderiv ℝ (windowContour hκ r (cutSeq L l) h)) v ∧
          ∀ w q : L2T L,
            |((fderiv ℝ (fderiv ℝ (windowContour hκ r (cutSeq L l) h)) v) w) q| ≤
              C*(cutSeq L l)^(r+1)*‖w‖*‖q‖ := by
  exact QuantumNLS.Q07BUniformCutsR16.q07Buniformcuts hκ hs B hh r

end QuantumNLS.RB90ASpec
#print axioms QuantumNLS.RB90ASpec.q07Buniformcuts_spec
