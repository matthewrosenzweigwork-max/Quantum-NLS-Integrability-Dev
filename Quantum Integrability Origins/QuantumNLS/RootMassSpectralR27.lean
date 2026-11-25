import QuantumNLS.RootWeightedMassesR26

/-! Bounded spectral deficits for R-0191D778. No spectral moment is assumed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootMassSpectralR27
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedMomentsR26
variable {L κ : ℝ} [Fact (0 < L)]

def deficit (Y x : ℝ) : ℝ := x^2/(Y^2+x^2)
def weight (Y p : ℝ) : ℝ := min 1 (p^2/Y^2)

lemma deficit_nonneg (Y x : ℝ) : 0 ≤ deficit Y x := by unfold deficit; positivity
lemma deficit_le_one {Y : ℝ} (hY : 0 < Y) (x : ℝ) : deficit Y x ≤ 1 := by
  unfold deficit
  exact (div_le_one (by positivity)).mpr (by nlinarith)
lemma weight_nonneg (Y p : ℝ) : 0 ≤ weight Y p := le_min (by norm_num) (by positivity)
lemma weight_le_one (Y p : ℝ) : weight Y p ≤ 1 := min_le_left _ _
lemma continuous_deficit {Y : ℝ} (hY : 0 < Y) : Continuous (deficit Y) := by
  exact (continuous_id.pow 2).div (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
lemma continuous_weight (Y : ℝ) : Continuous (weight Y) :=
  continuous_const.min ((continuous_id.pow 2).div_const _)

lemma integrable_deficit (μ : Measure ℝ) [IsFiniteMeasure μ] {Y : ℝ} (hY : 0 < Y) :
    Integrable (deficit Y) μ := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_deficit hY).aestronglyMeasurable
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (deficit_nonneg Y x)]; exact deficit_le_one hY x)

lemma weight_summable (a : ActionTorus.PosL1) (Y : ℝ) :
    Summable (fun n : ℤ => weight Y (momentum L n)*a.1 n) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_nonneg _ _) (a.2 n))
    (fun n => ?_) (ActionTorus.summable_posL1 a)
  exact mul_le_of_le_one_left (a.2 n) (weight_le_one _ _)

lemma scalar_bound {Y : ℝ} (hY : 0 < Y) (x p : ℝ) :
    deficit Y x ≤ 2*weight Y p+2*(x-p)^2/Y^2 := by
  have hY2 : 0 < Y^2 := sq_pos_of_pos hY
  have hd : deficit Y x ≤ x^2/Y^2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) hY2 (by nlinarith)
  by_cases hp : 1 ≤ p^2/Y^2
  · rw [weight,min_eq_left hp]
    have hh := deficit_le_one hY x
    have hn : 0 ≤ 2*(x-p)^2/Y^2 := by positivity
    linarith
  · rw [weight,min_eq_right (le_of_not_ge hp)]
    apply hd.trans
    calc
      x^2/Y^2 ≤ (2*p^2+2*(x-p)^2)/Y^2 := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x-2*p)]) hY2.le
      _ = _ := by ring

lemma spectral_bound (hκ : 0 < κ) (u : L2T L) {Y : ℝ} (hY : 0 < Y) :
    (∫ x, deficit Y x ∂PhysicalQuantumMeasure.measure hκ u) ≤
      2*(∑' n : ℤ,weight Y (momentum L n)*(RootIndexedMasses.masses hκ u).1 n)+
        2*κ*‖u‖^4/(L*Y^2) := by
  let μ := PhysicalQuantumMeasure.measure hκ u
  have hw : Integrable (fun x => weight Y (cellMomentum hκ u x)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((continuous_weight Y).measurable.comp (measurable_cellMomentum hκ u)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg _ _)] using weight_le_one Y (cellMomentum hκ u x))
  have hi : Integrable (fun n => weight Y (momentum L n)) (indexLaw hκ u) := by
    apply (integrable_indexLaw_iff hκ u _).mpr
    simpa only [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg _ _),mul_comm] using weight_summable (L := L) (RootIndexedMasses.masses hκ u) Y
  have he : (∫ x,weight Y (cellMomentum hκ u x) ∂μ) =
      ∑' n : ℤ,weight Y (momentum L n)*(RootIndexedMasses.masses hκ u).1 n := by
    have hm := integral_map (μ := μ) (measurable_cellIndex hκ u).aemeasurable
      (Measurable.of_discrete (f := fun n => weight Y (momentum L n))).aestronglyMeasurable
    change (∫ x,weight Y (momentum L (cellIndex hκ u x)) ∂μ) = _
    rw [← hm]
    exact (integral_indexLaw hκ u _ hi).trans (tsum_congr fun _ => mul_comm _ _)
  have hd := integrable_displacement hκ u
  have hb := (displacement_bound hκ u).2
  calc
    _ ≤ ∫ x, 2*weight Y (cellMomentum hκ u x)+2*(x-cellMomentum hκ u x)^2/Y^2 ∂μ :=
      integral_mono (integrable_deficit μ hY) ((hw.const_mul 2).add ((hd.const_mul 2).div_const _))
        (fun x => scalar_bound hY x _)
    _ = 2*(∑' n : ℤ,weight Y (momentum L n)*(RootIndexedMasses.masses hκ u).1 n)+
        2*displacement hκ u/Y^2 := by
      rw [integral_add (hw.const_mul 2) ((hd.const_mul 2).div_const _),integral_const_mul,
        integral_div,integral_const_mul,he]
      rfl
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 2)) (sq_nonneg Y)
      dsimp [displacement] at hh ⊢
      nlinarith [show 2*(κ*‖u‖^4/L)/Y^2 = 2*κ*‖u‖^4/(L*Y^2) by ring]
end QuantumNLS.RootMassSpectralR27
