import QuantumNLS.TerraMultiRound59SignedCharges

/-! Physical scalar expansion with the minimal-order signed polynomials. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound59SignedExpansion
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RootH1RatioBounds QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound59RealExpansion QuantumNLS.TerraMultiRound59SignedCharges

theorem physical_signed_expansion (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (∀ᶠ Y : ℝ in atTop, ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
        ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
          retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1))
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  obtain ⟨x, ha0, r, hx, hr, he⟩ := physical_ratio_real_expansion L s hs κ hκ u hu
  refine ⟨x, ha0, r, hx, hr, ?_⟩
  apply he.congr'
  · filter_upwards with Y
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [odd_coefficient_signed (L := L) s hs κ x j hj'.1 hj'.2]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

#print axioms physical_signed_expansion
end QuantumNLS.TerraMultiRound59SignedExpansion
