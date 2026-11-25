import NlsGge.GK38.AbelianHilbert

/-! UNCOMPILED finite-mass limit prerequisite for constructing the actual full
period map. No bounded limit operator or summability oracle is assumed. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6CoordinateLimit_l2_mass38 {ι : Type*} (f : ℕ → ι → ℂ)
    (g : ι → ℂ) (B : ℝ)
    (hb : ∀ k : ℕ, ∀ S : Finset ι, (∑ m ∈ S, ‖f k m‖^2) ≤ B)
    (ht : ∀ m : ι, Tendsto (fun k : ℕ => f k m) atTop (𝓝 (g m))) :
    Summable (fun m : ι => ‖g m‖^2) ∧ (∑' m : ι, ‖g m‖^2) ≤ B := by
  have hfinite (S : Finset ι) : (∑ m ∈ S, ‖g m‖^2) ≤ B := by
    have hlim : Tendsto (fun k : ℕ => ∑ m ∈ S, ‖f k m‖^2) atTop
        (𝓝 (∑ m ∈ S, ‖g m‖^2)) :=
      tendsto_finsetSum S (fun m _hm => (ht m).norm.pow 2)
    exact le_of_tendsto' hlim (fun k => hb k S)
  have hmem : Memℓp g 2 := memℓp_gen' (C := B) (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hfinite)
  have hs : Summable (fun m : ι => ‖g m‖^2) := by
    have hh := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp hmem
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hh
  exact ⟨hs,le_of_tendsto' hs.hasSum hfinite⟩

end
end NlsGge.GK38
