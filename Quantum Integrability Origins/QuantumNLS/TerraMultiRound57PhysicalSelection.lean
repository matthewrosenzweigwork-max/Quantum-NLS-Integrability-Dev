import QuantumNLS.TerraMultiRound57Collection
import QuantumNLS.TerraMultiRound43REG005

/-! Select a branch with the REG-005 physical ratio agreement and transport
the tree expansion to that same branch. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57PhysicalSelection
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound39AlgebraBall
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound43REG005
open QuantumNLS.TerraMultiRound57Collection QuantumNLS.TerraMultiRound57LevelIdentity

/-- The finite tree expansion belongs to the REG-005 physical ratio branch;
no coefficient identification or polynomial extension is asserted here. -/
theorem physical_ratio_tree_expansion (L : ℝ) [hLf : Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (∀ᶠ Y : ℝ in atTop, ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (fun Y : ℝ => scalar L (s - 1 : ℕ) x (r Y) -
        (freeScalar (L := L) (s - 1 : ℕ) x Y +
          (∑ n ∈ Finset.Ico 1 s, positiveApprox (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y) +
          leadingApprox (L := L) (k := s - 1) κ x s Y))
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  classical
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
    linarith
  obtain ⟨x, ha0, hx, hpar, hagree, _⟩ := signed_small_solutions_and_parity L (s - 1 : ℕ) ha κ hκ u hu
  obtain ⟨B, hB, hb⟩ := hpar
  obtain ⟨C, hC, hc⟩ := hagree
  have hex : ∀ Y : ℝ, ∃ r : Ell2, max B C ≤ Y →
      (∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 r = ratioL2 hY hlog hκ.le u hsmall) ∧
      (∀ (hY : 0 < |Y|) (t : Ell2), ‖t‖ ≤ 2 * ‖x‖ / |Y| →
        physicalT hLf.out ha hY κ x t = t → t = r) := by
    intro Y
    by_cases hYB : max B C ≤ Y
    · have hBY : B ≤ |Y| := (le_max_left B C).trans (hYB.trans (le_abs_self Y))
      have hCY : C ≤ Y := (le_max_right B C).trans hYB
      have hYpos : 0 < Y := hC.trans_le hCY
      obtain ⟨hY, r, z, hrn, hzn, hr, hz, hrode, hrp, hzode, hzp, hrg, hzg, hru, hzu, hp⟩ := hb Y hBY
      have hnr : algebraNorm L (s - 1 : ℕ) r ≤ 2 * algebraNorm L (s - 1 : ℕ) x / Y := by
        simpa [abs_of_pos hYpos] using hrn
      obtain ⟨hlog, hsmall, hratio⟩ := hc Y hCY r hnr hYpos hr
      refine ⟨r, fun _ => ⟨⟨hYpos, hlog, hsmall, hratio⟩, ?_⟩⟩
      intro hY' t ht hf
      apply hru t _ hf
      unfold algebraNorm
      have hh := mul_le_mul_of_nonneg_left ht (algebraScale_pos L (s - 1 : ℕ)).le
      convert hh using 1
      ring
    · exact ⟨0, fun h => False.elim (hYB h)⟩
  choose r hr using hex
  have he : ∀ᶠ Y : ℝ in atTop,
      (∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (∀ (hY : 0 < |Y|) (t : Ell2), ‖t‖ ≤ 2 * ‖x‖ / |Y| →
        physicalT hLf.out ha hY κ x t = t → t = r Y) := by
    filter_upwards [eventually_ge_atTop (max B C)] with Y hY
    exact hr Y hY
  refine ⟨x, ha0, r, hx, ?_, ?_⟩
  · exact he.mono (fun _ h => h.1)
  · apply scalar_tree_expansion (L := L) s hs κ x r
    exact he.mono (fun _ h => h.2)

#print axioms physical_ratio_tree_expansion
end QuantumNLS.TerraMultiRound57PhysicalSelection
