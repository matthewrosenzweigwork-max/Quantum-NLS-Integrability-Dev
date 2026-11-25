import NlsGge.ThirdConsultation.G1.G1098M2F
import NlsGge.ThirdConsultation.G1.G1098M2C
import NlsGge.ThirdConsultation.G1.G1098M2CT
import NlsGge.ThirdConsultation.G1.G1098M2DE
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.IsolatingTopology

/-! # G1-098 M2h (assembly), proof development (AUTHOR; not reviewed).
Pro round 9 section 13 helper `complexMixedColumn_local_square_sum`, in the stronger form: an open
neighbourhood `U` of the real centre pair, contained in `gkW ×ˢ gkW`, with a nonnegative constant.
`U := interior (Uφ ×ˢ Uψ)`, where `Uφ` is the intersection of the shift-bound and square-sum
neighbourhoods of `muSeq_local_bounds38` and `muSeq_local_l2_38` with a unit ball and `gkW`.
Uniform constants: shift `c`, square-sum `S`, radius `R` (common to both factors), then `CD`, `CT`
from the M2c state bounds, then the finite-sum bound of M2e and the column bound of M2f.
No hypothesis beyond the stated M2 inputs is added. -/
set_option autoImplicit false
open NlsGge.Pilot
open Filter Topology MeasureTheory Set Metric
open NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.G1098M2C
  NlsGge.ThirdConsultation.G1098M2CT NlsGge.ThirdConsultation.G1098M2DE
  NlsGge.ThirdConsultation.G1098M2F
namespace NlsGge.ThirdConsultation.G1098M2H
noncomputable section

theorem norm_le_of_mem_ball_one {x x0 : PotPair} (h : x ∈ ball x0 1) : ‖x‖ ≤ ‖x0‖ + 1 := by
  have h1 : ‖x - x0‖ < 1 := by
    rw [← dist_eq_norm]
    exact mem_ball.mp h
  have h2 := norm_sub_norm_le x x0
  linarith

/-- M2 helper (Pro round 9 section 13, stronger form): local square summability of the complex
mixed column errors on an open neighbourhood of the real centre pair, inside `gkW ×ˢ gkW`. -/
theorem complexMixedColumn_local_square_sum (u₀ v₀ : PhysicalL2) :
    ∃ U : Set (PotPair × PotPair),
      U ∈ 𝓝 (realSlice u₀, realSlice v₀) ∧ IsOpen U ∧ U ⊆ gkW ×ˢ gkW ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ p : PotPair × PotPair, p ∈ U →
          Summable (fun j : ℤ × Bool =>
            ‖complexMixedColumn p.1 p.2 j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ∧
          (∑' j : ℤ × Bool, ‖complexMixedColumn p.1 p.2 j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ≤ C := by
  obtain ⟨Ub, hUb, Nb, _hNb, hbφ⟩ := muSeq_local_bounds38 (realSlice u₀)
  obtain ⟨Ub', hUb', Nb', _hNb', hbψ⟩ := muSeq_local_bounds38 (realSlice v₀)
  obtain ⟨U2, hU2, C2, _hC2, h2⟩ := muSeq_local_l2_38 (realSlice u₀)
  obtain ⟨U2', hU2', C2', _hC2', h2'⟩ := muSeq_local_l2_38 (realSlice v₀)
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, 2 * (Nb : ℝ) * Real.pi + Real.pi / 4 ≤ c ∧
      2 * (Nb' : ℝ) * Real.pi + Real.pi / 4 ≤ c :=
    ⟨max _ _, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨S, hS1, hS2⟩ : ∃ S : ℝ, C2 ≤ S ∧ C2' ≤ S := ⟨max C2 C2', le_max_left _ _, le_max_right _ _⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ‖realSlice u₀‖ + ‖realSlice v₀‖ + 1 ≤ R := ⟨_, le_rfl⟩
  obtain ⟨CD, hCD⟩ := complexDirState_sub_l2 R c S
  obtain ⟨CT, hCT⟩ := complexTerminalState_sub_l2 R c S
  have hUφ : Ub ∩ U2 ∩ ball (realSlice u₀) 1 ∩ gkW ∈ 𝓝 (realSlice u₀) :=
    inter_mem (inter_mem (inter_mem hUb hU2) (ball_mem_nhds _ zero_lt_one))
      (isOpen_gkW.mem_nhds (realSlice_mem_gkW u₀))
  have hUψ : Ub' ∩ U2' ∩ ball (realSlice v₀) 1 ∩ gkW ∈ 𝓝 (realSlice v₀) :=
    inter_mem (inter_mem (inter_mem hUb' hU2') (ball_mem_nhds _ zero_lt_one))
      (isOpen_gkW.mem_nhds (realSlice_mem_gkW v₀))
  have hsub : interior ((Ub ∩ U2 ∩ ball (realSlice u₀) 1 ∩ gkW) ×ˢ
      (Ub' ∩ U2' ∩ ball (realSlice v₀) 1 ∩ gkW)) ⊆
      (Ub ∩ U2 ∩ ball (realSlice u₀) 1 ∩ gkW) ×ˢ (Ub' ∩ U2' ∩ ball (realSlice v₀) 1 ∩ gkW) :=
    interior_subset
  refine ⟨interior ((Ub ∩ U2 ∩ ball (realSlice u₀) 1 ∩ gkW) ×ˢ
      (Ub' ∩ U2' ∩ ball (realSlice v₀) 1 ∩ gkW)),
    interior_mem_nhds.mpr (prod_mem_nhds hUφ hUψ), isOpen_interior,
    fun p hp => Set.mk_mem_prod ((hsub hp).1.2) ((hsub hp).2.2),
    max (2 * ((2 * (3 + CD) ^ 2 + 4 * (5 + CT) ^ 2 + 16) * (2 * CD + 2 * CT))) 0,
    le_max_right _ _, ?_⟩
  intro p hp
  obtain ⟨hp1, hp2⟩ := hsub hp
  have hφb : ∀ n : ℤ, ‖muSeq p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c := fun n =>
    ((hbφ p.1 hp1.1.1.1 n).1).trans hc1
  have hψb : ∀ n : ℤ, ‖muSeq p.2 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c := fun n =>
    ((hbψ p.2 hp2.1.1.1 n).1).trans hc2
  have hφs := h2 p.1 hp1.1.1.2
  have hψs := h2' p.2 hp2.1.1.2
  have hφT : (∑' n : ℤ, ‖muSeq p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ S := hφs.2.trans hS1
  have hψT : (∑' n : ℤ, ‖muSeq p.2 n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ S := hψs.2.trans hS2
  have hr1 : ‖p.1‖ ≤ R :=
    (norm_le_of_mem_ball_one hp1.1.2).trans (by linarith [norm_nonneg (realSlice v₀)])
  have hr2 : ‖p.2‖ ≤ R :=
    (norm_le_of_mem_ball_one hp2.1.2).trans (by linarith [norm_nonneg (realSlice u₀)])
  have hD1 := hCD p.1 hr1 hφb hφs.1 hφT
  have hD2 := hCD p.2 hr2 hψb hψs.1 hψT
  have hT1 := hCT p.1 hr1 hφb hφs.1 hφT
  have hT2 := hCT p.2 hr2 hψb hψs.1 hψT
  have hC : ∀ t : Set.Icc (0 : ℝ) 1, ∀ T : Finset (ℤ × Bool),
      ∑ j ∈ T, ‖(complexMixedKernel p.1 p.2 j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) t 0‖ ^ 2 ≤
        2 * ((2 * (3 + CD) ^ 2 + 4 * (5 + CT) ^ 2 + 16) * (2 * CD + 2 * CT)) :=
    fun t T => mixed_finite_sum_bound p.1 p.2 t CD CT (hD1 t) (hD2 t) (hT1 t) (hT2 t) T
  have hcol := mixedColumn_error_summable p.1 p.2 _ hC
  exact ⟨hcol.1, hcol.2.trans (le_max_left _ _)⟩

/-- CHECK02 form of M2 (weaker: no openness or inclusion clause), as a corollary of the helper. -/
theorem M2_stmt_of_helper : ∀ u₀ v₀ : PhysicalL2, ∃ U : Set (PotPair × PotPair),
    U ∈ 𝓝 (realSlice u₀, realSlice v₀) ∧
    ∃ C : ℝ, ∀ p : PotPair × PotPair, p ∈ U →
      Summable (fun j : ℤ × Bool =>
        ‖complexMixedColumn p.1 p.2 j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ∧
      (∑' j : ℤ × Bool, ‖complexMixedColumn p.1 p.2 j.1 j.2 - mixedReference j.1 j.2‖ ^ 2) ≤ C := by
  intro u₀ v₀
  obtain ⟨U, hU, _, _, C, _, h⟩ := complexMixedColumn_local_square_sum u₀ v₀
  exact ⟨U, hU, C, h⟩

end
end NlsGge.ThirdConsultation.G1098M2H
