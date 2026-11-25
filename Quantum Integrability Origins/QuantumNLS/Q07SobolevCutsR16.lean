import QuantumNLS.Q07PhysicalProfilesR15
import QuantumNLS.Ext025A3Compact

/-! The actual DEF-002 Sobolev ball has compact closure in physical L2.
This binds the real-cut checkpoint to the printed Sobolev class, including
radial variations and a fixed full L2 neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Metric Filter Topology
namespace QuantumNLS.Q07SobolevCutsR16
open Sobolev Sobolev.PosWeight PhysicalTensor
variable {L κ s : ℝ} [Fact (0 < L)]

/-- Inclusion through the proved normalized Fourier equivalence. -/
def inclusion (hs : 0 ≤ s) : H02 L s →L[ℂ] L2T L := fieldToL2 (one_le_def002 L hs)

/-- The physical Sobolev inclusion is compact, by the proved Fourier heads
and uniformly vanishing weighted tails of ROOT-01. -/
theorem compact_inclusion (hs : 0 < s) : IsCompactOperator (inclusion (L := L) hs.le) := by
  let e := fourierHs (L := L) (one_le_def002 L hs.le)
  let e0 := (fourierHs (L := L) (one_le_def002 L (s := 0) le_rfl)).symm
  let j := (fieldToL2 (L := L) (one_le_def002 L (s := 0) le_rfl)).comp
    e0.toContinuousLinearEquiv.toContinuousLinearMap
  have hc := ((Ext025A3.root01_def002_compact (Fact.out : 0 < L) hs).comp_clm
    e.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp j
  have heq : j.comp ((h02_mono L hs.le).comp e.toContinuousLinearEquiv.toContinuousLinearMap) =
      inclusion (L := L) hs.le := by
    apply ContinuousLinearMap.ext
    intro u
    apply (QuantumNLS.Fourier.fourierL2 L).injective
    ext n
    have h := fourierHs_val (L := L) (one_le_def002 L (s := 0) le_rfl)
      (e0 (h02_mono L hs.le (e u))) n
    rw [show fourierHs (L := L) (one_le_def002 L (s := 0) le_rfl)
      (e0 (h02_mono L hs.le (e u))) = h02_mono L hs.le (e u) from
        (fourierHs (L := L) (one_le_def002 L (s := 0) le_rfl)).apply_symm_apply _] at h
    exact h.symm
  change IsCompactOperator (j.comp ((h02_mono L hs.le).comp e.toContinuousLinearEquiv.toContinuousLinearMap)) at hc
  rw [heq] at hc
  exact hc

def sobolevClass (s B : ℝ) : Set (L2T L) :=
  {u | ∃ v : H02 L s, ‖v‖ ≤ B ∧ v.val = u}

theorem class_eq_image (hs : 0 ≤ s) (B : ℝ) :
    sobolevClass (L := L) s B = inclusion hs '' closedBall 0 B := by
  ext u
  simp only [sobolevClass, mem_ofPred_eq, mem_image, mem_closedBall, dist_zero_right]
  rfl

/-- Compact closure in physical L2; no compactness of the infinite-dimensional
Sobolev ball in its own norm is asserted. -/
theorem compact_closure (hs : 0 < s) (B : ℝ) :
    IsCompact (closure (sobolevClass (L := L) s B)) := by
  rw [class_eq_image hs.le]
  exact (compact_inclusion hs).isCompact_closure_image_closedBall B

/-- Uniform real cuts and actual full-mass measure gaps for the entire bounded
Sobolev class, a stronger profile scope than the smooth subclass. -/
theorem uniform_sobolev_measure_cuts (hκ : 0 < κ) (hs : 0 < s) (B : ℝ) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ sobolevClass (L := L) s B, ∀ a : ℝ,
      (a = PROP017UniformN.cutSeq L l ∨ a = -PROP017UniformN.cutSeq L l) →
      (∀ t : ℝ, |t| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) u (a+t)| < 3/2) ∧
      |PhysicalL2BandGeometry.d (κ := κ) u a| ≤ 1/2 ∧
      FullMass.Mmeas κ u (Ioo (a-1/L) (a+1/L)) = 0 := by
  obtain ⟨l0, hl0⟩ := Q07PhysicalProfilesR15.uniform_physical_measure_cuts hκ (compact_closure (L := L) hs B)
  exact ⟨l0, fun l hl u hu => hl0 l hl u (subset_closure hu)⟩

/-- One positive physical radius and one cut threshold work for the entire
Sobolev class and its full real L2 neighborhood. -/
theorem uniform_sobolev_cuts_near (hκ : 0 < κ) (hs : 0 < s) (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      ∀ u ∈ sobolevClass (L := L) s B, ∀ v : L2T L, ‖v-u‖ < δ → ∀ a : ℝ,
      (a = PROP017UniformN.cutSeq L l ∨ a = -PROP017UniformN.cutSeq L l) →
      (∀ t : ℝ, |t| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) v (a+t)| < 3/2) ∧
      |PhysicalL2BandGeometry.d (κ := κ) v a| ≤ 1/2 ∧
      FullMass.Mmeas κ v (Ioo (a-1/L) (a+1/L)) = 0 := by
  obtain ⟨δ, hδ, l0, hl0⟩ := Q07PhysicalProfilesR15.uniform_physical_cuts_near
    (κ := κ) (compact_closure (L := L) hs B)
  refine ⟨δ, hδ, l0, fun l hl u hu v hv a ha => ?_⟩
  obtain ⟨hc, hb⟩ := hl0 l hl u (subset_closure hu) v hv a ha
  exact ⟨hc, hb, Q07PhysicalProfilesR15.measure_gap_of_real_cut hκ v hc⟩

end QuantumNLS.Q07SobolevCutsR16
