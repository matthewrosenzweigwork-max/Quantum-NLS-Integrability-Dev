import QuantumNLS.RootMassSpectralR27
import QuantumNLS.RootH1Ratio

/-! The physical Fourier resolvent deficit and the bounded Cauchy identity. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped InnerProductSpace
namespace QuantumNLS.RootMassFourierR27
open PhysicalTensor (L2T)
open QuantumNLS.Fourier RootWeightedCellsR26 RootMassSpectralR27
open RootH1RatioOperator RootH1RatioModes RootH1RatioStrong
variable {L κ : ℝ} [Fact (0 < L)]

lemma resolvent_coeff {Y : ℝ} (hY : 0 < Y) (u : L2T L) (n : ℤ) :
    fourierL2 L (resolvent Y u) n = ((Y:ℂ)+omega L n)⁻¹ * fourierL2 L u n := by
  let F : L2T L →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    ((fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.comp (resolvent Y))
  have hs := F.hasSum (hasSum_coeff_smul_modeLp L u)
  have he : (fun k : ℤ => F (coeff L u k • modeLp L k)) =
      fun k => if k=n then ((Y:ℂ)+omega L n)⁻¹ * fourierL2 L u n else 0 := by
    funext k
    by_cases h : k=n
    · subst k
      simp [F,resolvent_mode hY,fourierL2_modeLp,fourierL2_apply,lp.evalCLM,lp.single_apply,mul_comm]
    · simp [F,resolvent_mode hY,fourierL2_modeLp,lp.evalCLM,lp.single_apply,h,Ne.symm h]
  rw [he] at hs
  exact hs.unique (hasSum_ite_eq n _)

lemma multiplier_real (Y p : ℝ) (c : ℂ) :
    (conj c * ((Y:ℂ)*((Y:ℂ)+Complex.I*(p:ℂ))⁻¹*c)).re =
      (Y^2/(Y^2+p^2))*‖c‖^2 := by
  have hr : ((Y:ℂ)+Complex.I*(p:ℂ)).re = Y := by simp
  have hi : ((Y:ℂ)+Complex.I*(p:ℂ)).im = p := by simp
  rw [show conj c * ((Y:ℂ)*((Y:ℂ)+Complex.I*(p:ℂ))⁻¹*c) =
      (Y:ℂ)*((conj c*c)/((Y:ℂ)+Complex.I*(p:ℂ))) by ring]
  rw [Complex.conj_mul',← Complex.ofReal_pow]
  simp [Complex.mul_re,Complex.div_re,Complex.normSq_apply,hr,hi,-Complex.ofReal_pow]
  ring

lemma fourier_deficit {Y : ℝ} (hY : 0 < Y) (u : L2T L) :
    (∑' n : ℤ,deficit Y (momentum L n)*‖fourierL2 L u n‖^2) =
      ‖u‖^2-(inner ℂ u (rescaled Y u)).re := by
  let a := fourierL2 L u
  let b := fourierL2 L (rescaled Y u)
  have hs := Energy.summable_sq a
  have hp := lp.summable_inner (𝕜 := ℂ) a b
  have hb (n : ℤ) : b n = (Y:ℂ)*((Y:ℂ)+Complex.I*(momentum L n:ℂ))⁻¹*a n := by
    change fourierL2 L ((Y:ℂ) • resolvent Y u) n = _
    rw [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,resolvent_coeff hY]
    have ho : omega L n = Complex.I*(momentum L n:ℂ) := by
      unfold omega momentum
      push_cast
      ring
    rw [ho]
    dsimp [a]
    ring
  have he (n : ℤ) : (inner ℂ (a n) (b n)).re =
      (Y^2/(Y^2+momentum L n^2))*‖a n‖^2 := by
    rw [RCLike.inner_apply',hb]
    exact multiplier_real _ _ _
  have hh : (inner ℂ u (rescaled Y u)).re =
      ∑' n : ℤ,(Y^2/(Y^2+momentum L n^2))*‖a n‖^2 := by
    rw [← (fourierL2 L).inner_map_map,lp.inner_eq_tsum,Complex.re_tsum hp]
    exact tsum_congr he
  have ht : Summable (fun n : ℤ => (Y^2/(Y^2+momentum L n^2))*‖a n‖^2) := by
    have h := (Complex.hasSum_re hp.hasSum).summable
    simpa only [he] using h
  have hn : ‖u‖^2 = ∑' n : ℤ,‖a n‖^2 := by
    rw [← norm_fourierL2 L u]; exact Energy.norm_sq_eq_tsum _
  rw [hh,hn,← hs.tsum_sub ht]
  apply tsum_congr
  intro n
  unfold deficit
  have hd : Y^2+momentum L n^2 ≠ 0 := by positivity
  dsimp [a]
  field_simp
  ring

lemma spectral_deficit (hκ : 0 < κ) (u : L2T L) {Y : ℝ} (hY : 0 < Y) :
    (∫ x,deficit Y x ∂PhysicalQuantumMeasure.measure hκ u) =
      ‖u‖^2+Y*(CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)).im := by
  let μ := PhysicalQuantumMeasure.measure hκ u
  have hi := CauchyUniqueness.integrable_cauchyKernel μ
    (show 0 < ((Y:ℂ)*Complex.I).im by simpa using hY)
  have he (x : ℝ) : deficit Y x = 1+Y*(((Y:ℂ)*Complex.I-(x:ℂ))⁻¹).im := by
    simp only [deficit,Complex.inv_im,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    simp only [mul_zero,mul_one,sub_zero,zero_sub,add_zero]
    have hd : x^2+Y^2 ≠ 0 := by positivity
    field_simp
    ring
  change (∫ x,deficit Y x ∂μ) = _
  have hr : Integrable (fun x : ℝ => (((Y:ℂ)*Complex.I-(x:ℂ))⁻¹).im) μ := hi.im
  simp_rw [he]
  rw [integral_add (integrable_const 1) (hr.const_mul Y),integral_const_mul,
    integral_const,smul_eq_mul,mul_one]
  have hm : μ.real univ = ‖u‖^2 := PhysicalQuantumMeasure.full_mass hκ u
  have him := integral_im hi
  simp only [RCLike.im_to_complex] at him
  rw [hm,him]
  dsimp [μ]
  rw [PhysicalL2Normalization.measure_eq_Mmeas]
  rfl
end QuantumNLS.RootMassFourierR27
