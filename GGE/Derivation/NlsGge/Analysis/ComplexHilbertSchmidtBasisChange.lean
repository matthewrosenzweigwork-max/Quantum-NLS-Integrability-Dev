import NlsGge.Analysis.ComplexHilbertSchmidtBasisEnergy

/-!
NEW-F02.06: a finite complex Hilbert–Schmidt image-energy sum transfers between
all Hilbert bases without countability assumptions or an added codomain basis.
This proves a genuine basis-independent finite sum, not a source DVD bound.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal

noncomputable section

namespace NlsGge.Pilot

/-- Squared image norms of a complex rectangular bounded map have the same
finite sum in every supplied source Hilbert basis, once the sum in one basis
is summable. -/
theorem hasSum_norm_sq_apply_of_complex_hilbertBasis
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    HasSum (fun j : κ => ‖T (c j)‖ ^ 2)
      (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  obtain ⟨η, d, _⟩ := exists_hilbertBasis ℂ F
  let fb : ι → ℝ := fun i => ‖T (b i)‖ ^ 2
  let fc : κ → ℝ := fun j => ‖T (c j)‖ ^ 2
  have hfb_nonneg : ∀ i, 0 ≤ fb i := fun _ => sq_nonneg _
  have hfc_nonneg : ∀ j, 0 ≤ fc j := fun _ => sq_nonneg _
  have hfinite_b : (∑' i : ι, ENNReal.ofReal (fb i)) ≠ ∞ :=
    hb.tsum_ofReal_ne_top
  have henergy :
      (∑' i : ι, ENNReal.ofReal (fb i)) =
        ∑' j : κ, ENNReal.ofReal (fc j) := by
    exact complex_ennreal_source_basis_energy_eq T b c d
  have hfinite_c : (∑' j : κ, ENNReal.ofReal (fc j)) ≠ ∞ := by
    rw [← henergy]
    exact hfinite_b
  have hfinite_c_nn :
      (∑' j : κ, (Real.toNNReal (fc j) : ℝ≥0∞)) ≠ ∞ := by
    simpa only [← ENNReal.ofNNReal_toNNReal] using hfinite_c
  have hfc_nn : Summable (fun j : κ => Real.toNNReal (fc j)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hfinite_c_nn
  have hfc_coe : Summable (fun j : κ => (Real.toNNReal (fc j) : ℝ)) :=
    NNReal.summable_coe.mpr hfc_nn
  have hfc_summable : Summable fc := by
    refine hfc_coe.congr fun j => ?_
    simp [Real.coe_toNNReal', max_eq_left (hfc_nonneg j)]
  have hreal_energy :
      ENNReal.ofReal (∑' i : ι, fb i) =
        ENNReal.ofReal (∑' j : κ, fc j) := by
    calc
      ENNReal.ofReal (∑' i : ι, fb i) =
          ∑' i : ι, ENNReal.ofReal (fb i) :=
        ENNReal.ofReal_tsum_of_nonneg hfb_nonneg hb
      _ = ∑' j : κ, ENNReal.ofReal (fc j) := henergy
      _ = ENNReal.ofReal (∑' j : κ, fc j) :=
        (ENNReal.ofReal_tsum_of_nonneg hfc_nonneg hfc_summable).symm
  have hsum_b_nonneg : 0 ≤ ∑' i : ι, fb i := tsum_nonneg hfb_nonneg
  have hsum_c_nonneg : 0 ≤ ∑' j : κ, fc j := tsum_nonneg hfc_nonneg
  have hreal_sum : (∑' i : ι, fb i) = ∑' j : κ, fc j :=
    (ENNReal.ofReal_eq_ofReal_iff hsum_b_nonneg hsum_c_nonneg).mp hreal_energy
  change HasSum fc (∑' i : ι, fb i)
  rw [hreal_sum]
  exact hfc_summable.hasSum

end NlsGge.Pilot
