import QuantumNLS.RootMassFourierR27

/-! The exact Fourier-tail estimate of R-0191D778. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.RootMassBoundR27
open PhysicalTensor (L2T)
open QuantumNLS.Fourier RootMassSpectralR27 RootMassFourierR27 RootWeightedCellsR26
open RootH1RatioOperator RootH1RatioBounds RootH1RatioStrong
variable {L κ : ℝ} [Fact (0 < L)]

def fourierTail (Y : ℝ) (u : L2T L) : ℝ :=
  ∑' n : {n : ℤ // Y ≤ |momentum L n|},‖fourierL2 L u n‖^2

lemma summable_deficit {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    Summable (fun n : ℤ => deficit Y (momentum L n)*‖fourierL2 L u n‖^2) :=
  (Energy.summable_sq (fourierL2 L u)).of_nonneg_of_le
    (fun _ => mul_nonneg (deficit_nonneg _ _) (sq_nonneg _))
    (fun _ => mul_le_of_le_one_left (sq_nonneg _) (deficit_le_one hY _))

lemma tail_le_deficit {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    fourierTail Y u ≤ 2*(∑' n : ℤ,deficit Y (momentum L n)*‖fourierL2 L u n‖^2) := by
  have hs := summable_deficit hY u
  have hb : ∀ n : {n : ℤ // Y ≤ |momentum L n|},
      ‖fourierL2 L u n‖^2 ≤ 2*(deficit Y (momentum L n)*‖fourierL2 L u n‖^2) := by
    intro n
    have hp : Y^2 ≤ momentum L n^2 := by
      simpa only [sq_abs] using (pow_le_pow_left₀ hY.le n.2 2)
    have hd : 1 ≤ 2*deficit Y (momentum L n) := by
      unfold deficit
      have hh : 0 < Y^2+momentum L n^2 := by positivity
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hh).mpr
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖fourierL2 L u n‖)]
  calc
    _ ≤ ∑' n : {n : ℤ // Y ≤ |momentum L n|},2*(deficit Y (momentum L n)*‖fourierL2 L u n‖^2) :=
      ((Energy.summable_sq (fourierL2 L u)).comp_injective Subtype.val_injective).tsum_le_tsum hb
        ((hs.comp_injective Subtype.val_injective).mul_left 2)
    _ = 2*(∑' n : {n : ℤ // Y ≤ |momentum L n|},deficit Y (momentum L n)*‖fourierL2 L u n‖^2) := tsum_mul_left
    _ ≤ _ := by
      gcongr
      exact Summable.tsum_subtype_le _ _ (fun _ => mul_nonneg (deficit_nonneg _ _) (sq_nonneg _)) hs

lemma resolvent_deficit_bound (hκ : 0 < κ) (u : L2T L) {Y : ℝ}
    (hY0 : max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y) :
    (∑' n : ℤ,deficit Y (momentum L n)*‖fourierL2 L u n‖^2) ≤
      (∫ x,deficit Y x ∂PhysicalQuantumMeasure.measure hκ u)+4*κ*‖u‖^4/Y := by
  obtain ⟨hY,hlog,hsmall⟩ := RootH1RatioConvergence.height_spec u hY0
  by_cases hu : u=0
  · subst u
    simp only [map_zero,lp.coeFn_zero,Pi.zero_apply,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
      mul_zero,tsum_zero,zero_pow (by norm_num : 4 ≠ 0),zero_div,add_zero]
    exact integral_nonneg (fun x => deficit_nonneg Y x)
  let r := ratioL2 hY hlog hκ.le u hsmall
  have he := nonlinear_error hY hlog hκ.le u hsmall
  have hn : ‖(Y:ℂ) • r-rescaled Y u‖ ≤ 4*κ*‖u‖^3/Y := by
    simpa only [smul_sub,rescaled,smul_apply,r] using he
  have hj : (inner ℂ u ((Y:ℂ) • r)).re-(inner ℂ u (rescaled Y u)).re ≤ 4*κ*‖u‖^4/Y := by
    calc
      _ = (inner ℂ u ((Y:ℂ) • r-rescaled Y u)).re := by rw [inner_sub_right,Complex.sub_re]
      _ ≤ ‖inner ℂ u ((Y:ℂ) • r-rescaled Y u)‖ := Complex.re_le_norm _
      _ ≤ ‖u‖*‖(Y:ℂ) • r-rescaled Y u‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖*(4*κ*‖u‖^3/Y) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = _ := by ring
  have hc := RootH1RatioCauchy.ratio_cauchy hY hlog hκ u hu hsmall
  have hm : (∫ x,deficit Y x ∂PhysicalQuantumMeasure.measure hκ u) =
      ‖u‖^2-(inner ℂ u ((Y:ℂ) • r)).re := by
    rw [spectral_deficit hκ u hY,hc,inner_smul_right]
    simp only [neg_mul,Complex.neg_im,Complex.I_mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    dsimp [r]
    ring
  rw [fourier_deficit hY u,hm]
  linarith

/-- The printed Fourier-tail bound, with m² written as ‖u‖⁴. -/
theorem fourier_tail_bound (hκ : 0 < κ) (u : L2T L) {Y : ℝ}
    (hY0 : max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y) :
    fourierTail Y u ≤
      4*(∑' n : ℤ,weight Y (momentum L n)*(RootIndexedMasses.masses hκ u).1 n)+
        4*κ*‖u‖^4/(L*Y^2)+8*κ*‖u‖^4/Y := by
  have hY := (RootH1RatioConvergence.height_spec u hY0).1
  have h1 := tail_le_deficit hY u
  have h2 := resolvent_deficit_bound hκ u hY0
  have h3 := spectral_bound hκ u hY
  calc
    _ ≤ 2*(2*(∑' n : ℤ,weight Y (momentum L n)*(RootIndexedMasses.masses hκ u).1 n)+
        2*κ*‖u‖^4/(L*Y^2)+4*κ*‖u‖^4/Y) := by linarith only [h1,h2,h3]
    _ = _ := by ring
end QuantumNLS.RootMassBoundR27
