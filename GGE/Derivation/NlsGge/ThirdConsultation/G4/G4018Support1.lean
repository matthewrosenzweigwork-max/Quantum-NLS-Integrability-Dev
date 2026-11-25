import Mathlib
/- H215_PRODBOUND01 (proof development, AUTHOR; not self-reviewed).
   Generic product estimate used by G4-018 (Pro round 9 section 10, step 4):
   a finite product of complex factors with summable-type control
   sum_s ||f i - 1|| <= B satisfies ||prod|| <= exp B, and this passes to any
   SummationFilter limit of the partial products. No physics, no hypotheses beyond these. -/
set_option autoImplicit false

namespace NlsGge.G4018Support

theorem finset_prod_norm_le_exp {ι : Type*} (f : ι → ℂ) (s : Finset ι) (B : ℝ)
    (hB : ∑ i ∈ s, ‖f i - 1‖ ≤ B) :
    ‖∏ i ∈ s, f i‖ ≤ Real.exp B := by
  have hfac : ∀ i ∈ s, ‖f i‖ ≤ Real.exp ‖f i - 1‖ := by
    intro i _
    have h1 : f i = 1 + (f i - 1) := by ring
    have h2 : ‖f i‖ ≤ 1 + ‖f i - 1‖ := by
      calc ‖f i‖ = ‖1 + (f i - 1)‖ := by rw [← h1]
        _ ≤ ‖(1 : ℂ)‖ + ‖f i - 1‖ := norm_add_le _ _
        _ = 1 + ‖f i - 1‖ := by rw [norm_one]
    exact h2.trans (by linarith [Real.add_one_le_exp ‖f i - 1‖])
  calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := Finset.norm_prod_le s f
    _ ≤ ∏ i ∈ s, Real.exp ‖f i - 1‖ := by
        gcongr with i hi
        exact hfac i hi
    _ = Real.exp (∑ i ∈ s, ‖f i - 1‖) := (Real.exp_sum s _).symm
    _ ≤ Real.exp B := Real.exp_le_exp.mpr hB

theorem hasProd_norm_le_exp {ι : Type*} (f : ι → ℂ) (a : ℂ) (L : SummationFilter ι)
    [L.filter.NeBot] (hP : HasProd f a L) (B : ℝ)
    (hB : ∀ s : Finset ι, ∑ i ∈ s, ‖f i - 1‖ ≤ B) :
    ‖a‖ ≤ Real.exp B := by
  have hP' : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, f i) L.filter (nhds a) := hP
  have ht : Filter.Tendsto (fun s : Finset ι => ‖∏ i ∈ s, f i‖) L.filter (nhds ‖a‖) :=
    hP'.norm
  exact le_of_tendsto ht (Filter.Eventually.of_forall fun s => finset_prod_norm_le_exp f s B (hB s))

end NlsGge.G4018Support
