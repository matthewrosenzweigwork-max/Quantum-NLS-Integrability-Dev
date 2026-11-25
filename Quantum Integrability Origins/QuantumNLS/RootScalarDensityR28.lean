import QuantumNLS.RootMassPropernessR27
import QuantumNLS.RootHilbertQuantiles
import QuantumNLS.RootCoreDensity

/-! Local Hölder regularity of the actual all-L2 density. No cut definition is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace QuantumNLS.RootScalarDensityR28
open PhysicalTensor (L2T)
open RootDensityIdentification
variable {L κ : ℝ} [Fact (0 < L)]

lemma arcosh_sq_sub {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Real.arcosh a-Real.arcosh b)^2 ≤ 2*|a-b| := by
  suffices h : ∀ a b : ℝ, 1 ≤ b → b ≤ a →
      (Real.arcosh a-Real.arcosh b)^2 ≤ 2*(a-b) by
    rcases le_total b a with hba | hab
    · simpa [abs_of_nonneg (sub_nonneg.mpr hba)] using h a b hb hba
    · have hh := h b a ha hab
      nlinarith [abs_of_nonpos (sub_nonpos.mpr hab)]
  intro a b hb hba
  have ha := hb.trans hba
  let d := Real.arcosh a-Real.arcosh b
  have hd : 0 ≤ d := sub_nonneg.mpr ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hba)
  have hb0 := Real.arcosh_nonneg hb
  have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ d/2 by positivity)
  have hs0 := Real.sinh_nonneg_iff.mpr (show 0 ≤ d/2 by positivity)
  have hc : 1+d^2/2 ≤ Real.cosh d := by
    have hh := Real.cosh_two_mul (d/2)
    have hi := Real.cosh_sq_sub_sinh_sq (d/2)
    rw [show 2*(d/2)=d by ring] at hh
    nlinarith [sq_nonneg (Real.sinh (d/2)-d/2)]
  have hadd := Real.cosh_add (Real.arcosh b) d
  have he : Real.arcosh b+d = Real.arcosh a := by dsimp [d]; ring
  rw [he,Real.cosh_arcosh ha,Real.cosh_arcosh hb] at hadd
  have hp := mul_nonneg (Real.sinh_nonneg_iff.mpr hb0) (Real.sinh_nonneg_iff.mpr hd)
  have hq := mul_nonneg (show 0 ≤ b-1 by linarith) (show 0 ≤ Real.cosh d-1 by linarith [Real.one_le_cosh d])
  change d^2 ≤ _
  nlinarith

lemma density_holder (hκ : 0 < κ) (u : L2T L) (x : ℝ) :
    ∃ s ∈ 𝓝 x, ∃ C r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ HolderOnWith C r (dens κ u) s := by
  have hf : ContDiff ℝ 1 (fun y : ℝ => (L2SpatialTransfer.discriminant κ u (y : ℂ)).re) :=
    (RootCoreDensity.contDiff_re_Delta κ u).of_le (by norm_num)
  obtain ⟨K,s,hs,hK⟩ := hf.contDiffAt.exists_lipschitzOnWith (x := x)
  let c := (Real.pi*κ)⁻¹
  let C : ℝ≥0 := ⟨c*Real.sqrt K, by dsimp [c]; positivity⟩
  refine ⟨s,hs,C,1/2,by norm_num,by norm_num,?_⟩
  intro a ha b hb
  suffices H : dist (dens κ u a) (dens κ u b) ≤ (C:ℝ)*dist a b^((1/2:ℝ≥0):ℝ) by
    simpa only [edist_dist, ENNReal.ofReal_mul C.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg _)] using
      (ENNReal.ofReal_le_ofReal H)
  have ht := hK.dist_le_mul a ha b hb
  rw [Real.dist_eq,Real.dist_eq] at ht
  let A := max (|(L2SpatialTransfer.discriminant κ u (a : ℂ)).re|/2) 1
  let B := max (|(L2SpatialTransfer.discriminant κ u (b : ℂ)).re|/2) 1
  have hab : |A-B| ≤ (K:ℝ)*|a-b|/2 := by
    apply (abs_max_sub_max_le_abs _ _ 1).trans
    rw [← sub_div,abs_div,abs_two]
    exact div_le_div_of_nonneg_right ((abs_abs_sub_abs_le_abs_sub _ _).trans ht) (by norm_num)
  have har := arcosh_sq_sub (le_max_right _ _ : 1 ≤ A) (le_max_right _ _ : 1 ≤ B)
  have hh : |Real.arcosh A-Real.arcosh B| ≤ Real.sqrt ((K:ℝ)*|a-b|) := by
    have hsqrt := Real.sq_sqrt (mul_nonneg K.coe_nonneg (abs_nonneg (a-b)))
    nlinarith [sq_abs (Real.arcosh A-Real.arcosh B),Real.sqrt_nonneg ((K:ℝ)*|a-b|)]
  change |dens κ u a-dens κ u b| ≤ (C:ℝ)*|a-b|^((1/2:ℝ≥0):ℝ)
  simp only [dens,RootDensity.hfun_eq_arcosh_max,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos Real.pi_pos hκ))]
  calc
    _ ≤ c*Real.sqrt ((K:ℝ)*|a-b|) := mul_le_mul_of_nonneg_left hh (by dsimp [c]; positivity)
    _ = _ := by
      rw [Real.sqrt_mul K.coe_nonneg]
      change c*(Real.sqrt K*Real.sqrt |a-b|) =
        (c*Real.sqrt K)*|a-b|^((1/2:ℝ≥0):ℝ)
      norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      rw [← Real.sqrt_eq_rpow]
      ring

lemma density_bound (hκ : 0 < κ) (u : L2T L) :
    ∃ B : ℝ, ∀ x, |dens κ u x| ≤ B := by
  let c := ∫ s in (0:ℝ)..L, ‖L2SpatialTransfer.profile u s‖
  have hc : 0 ≤ c := intervalIntegral.integral_nonneg (Fact.out : 0 < L).le (fun _ _ => norm_nonneg _)
  refine ⟨c/(Real.pi*Real.sqrt κ),fun x => ?_⟩
  rw [abs_of_nonneg (dens_nonneg hκ u x)]
  exact RootDensity.rootDensity_le hκ hc (L1TraceGeometry.L2_abs_trace_le hκ u) x

lemma density_hyp (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    RootHilbert.HilbertHyp (dens κ u) := by
  obtain ⟨B,hB⟩ := density_bound hκ u
  exact ⟨dens_nonneg hκ u,(D05TotalVariation.integrable_dens hκ hu).1,
    memLp_top_of_bound (continuous_dens κ u).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x),
    density_holder hκ u⟩

lemma density_mass (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    ∫ x,dens κ u x = ‖u‖^2 := (D05TotalVariation.integrable_dens hκ hu).2

lemma density_measure (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    RootHilbert.rhoMeasure (dens κ u) = PhysicalQuantumMeasure.measure hκ u :=
  (root_density hκ hu).symm

end QuantumNLS.RootScalarDensityR28
