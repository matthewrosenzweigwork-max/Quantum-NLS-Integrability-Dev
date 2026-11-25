import QuantumNLS.RootWeightedPhysicalR26

/-! The physical first moment from the already proved H1 Riccati branch.
No smooth-input moment theorem or supplied Riccati conclusion is used. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiPicardBall QuantumNLS.RiccatiModeAnalytic
open QuantumNLS.RootEnergyMomentResolvent QuantumNLS.RootEnergyMomentBranch
open QuantumNLS.RootEnergyMomentPhysical QuantumNLS.RootEnergyMomentScalar
open QuantumNLS.SmoothScalarMomentsPositive QuantumNLS.PhysicalTensor
open QuantumNLS.ProductEnergyPreparation
namespace QuantumNLS.RootWeightedFirstR26
open RootWeightedPhysicalR26
variable {L : ℝ} [hLf : Fact (0 < L)]

def firstKernel (n : ℕ) (t : ℝ) : ℝ := t*kernel 0 n t

lemma firstKernel_bound (n : ℕ) (t : ℝ) : |firstKernel n t| ≤ |t| := by
  rw [firstKernel,abs_mul,abs_of_nonneg (kernel_nonneg 0 n t)]
  exact mul_le_of_le_one_right (abs_nonneg _) (kernel_zero_le_one n t)

lemma firstKernel_tendsto (t : ℝ) : Tendsto (fun n => firstKernel n t) atTop (𝓝 t) := by
  simpa only [firstKernel,Nat.mul_zero,pow_zero,mul_one] using (kernel_tendsto 0 t).const_mul t

lemma kernel_cauchy (n : ℕ) (t : ℝ) :
    firstKernel n t = -(y n)^2 * (((z n)-(t : ℂ))⁻¹).re := by
  rw [Complex.inv_re,Complex.normSq_apply]
  simp only [z,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
    sub_zero,zero_sub,add_zero]
  unfold firstKernel kernel y
  norm_num only [Nat.mul_zero,pow_zero,neg_sq]
  have hy : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp [hy]
  ring

lemma spectral_regularization (κ : ℝ) (u : L2T L) (n : ℕ) :
    (∫ t,firstKernel n t ∂FullMass.Mmeas κ u) =
      -(y n)^2*(EmpiricalRapidity.cauchyTransform (FullMass.Mmeas κ u) (z n)).re := by
  have hi := EmpiricalRapidity.integrable_cauchyIntegrand (FullMass.Mmeas κ u) (z n) (z_pos n).ne'
  unfold EmpiricalRapidity.cauchyTransform
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [← hre,← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun t => kernel_cauchy n t))

lemma spectral_limit {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Tendsto (fun n => -(y n)^2*(EmpiricalRapidity.cauchyTransform (FullMass.Mmeas κ u) (z n)).re)
      atTop (𝓝 (∫ t : ℝ,t ∂FullMass.Mmeas κ u)) := by
  have hx := (RootEnergyMomentScalar.scalar_energy_moment hκ u hH).1
  have hx2 := (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hx
  have ht := tendsto_integral_of_dominated_convergence (fun t : ℝ => |t|)
    (fun n => (show Continuous (firstKernel n) from continuous_id.mul (kernel_continuous 0 n)).aestronglyMeasurable)
    ((hx2.integrable (by norm_num)).abs)
    (fun n => ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using firstKernel_bound n t)
    (ae_of_all _ firstKernel_tendsto)
  simpa only [spectral_regularization] using ht

lemma multiplier_imaginary (n : ℕ) (p : ℝ) (c : ℂ) :
    -y n*(conj c*(c/(1+Complex.I*(p : ℂ)/(y n : ℂ)))).im =
      kernel 0 n p*p*‖c‖^2 := by
  let d : ℂ := 1+Complex.I*(p : ℂ)/(y n : ℂ)
  have hdre : d.re = 1 := by simp [d,Complex.mul_re]
  have hdim : d.im = p/y n := by simp [d,Complex.mul_im]
  change -y n*(conj c*(c/d)).im = _
  rw [← mul_div_assoc,Complex.conj_mul',← Complex.ofReal_pow,Complex.div_im]
  simp only [Complex.normSq_apply,hdre,hdim,Complex.ofReal_re,Complex.ofReal_im,zero_mul]
  unfold kernel y
  norm_num only [Nat.mul_zero,pow_zero]
  field_simp
  ring

lemma linear_regularization_first (u : L2T L) (hH : OneH1 u) (n : ℕ) :
    -y n*(floquetJ L 1 (base u hH) (scaledR L n (base u hH))).im =
      ∑' k : ℤ,kernel 0 n (QuantumNLS.Fourier.freq L k)*
        QuantumNLS.Fourier.freq L k*‖QuantumNLS.Fourier.fourierL2 L u k‖^2 := by
  let b := base u hH
  have hp : Summable (fun k => conj (toField L 1 b k)*toField L 1 (scaledR L n b) k) := by
    have h := lp.summable_inner (𝕜 := ℂ) (divEll L 1 (by norm_num) b)
      (divEll L 1 (by norm_num) (scaledR L n b))
    simpa only [RCLike.inner_apply',divEll_apply,toField,mul_comm] using h
  rw [floquetJ_fourier (by norm_num),Complex.im_tsum hp,← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [scaledR_field,multiplier_imaginary]
  rw [toField_base]
  rfl

lemma linear_limit (u : L2T L) (hH : OneH1 u) :
    Tendsto (fun n => -y n*(floquetJ L 1 (base u hH) (scaledR L n (base u hH))).im)
      atTop (𝓝 (fourierMomentum u)) := by
  simp_rw [linear_regularization_first]
  apply tendsto_tsum_of_dominated_convergence (bound := fun k =>
    |QuantumNLS.Fourier.freq L k*‖QuantumNLS.Fourier.fourierL2 L u k‖^2|)
    (momentum_summable u hH)
  · intro k
    simpa only [Nat.mul_zero,pow_zero,one_mul] using
      ((kernel_tendsto 0 (QuantumNLS.Fourier.freq L k)).mul_const
        (QuantumNLS.Fourier.freq L k)).mul_const (‖QuantumNLS.Fourier.fourierL2 L u k‖^2)
  · apply Eventually.of_forall
    intro n k
    rw [Real.norm_eq_abs,show kernel 0 n (QuantumNLS.Fourier.freq L k)*QuantumNLS.Fourier.freq L k*
        ‖QuantumNLS.Fourier.fourierL2 L u k‖^2 = kernel 0 n (QuantumNLS.Fourier.freq L k)*
        (QuantumNLS.Fourier.freq L k*‖QuantumNLS.Fourier.fourierL2 L u k‖^2) by ring,
      abs_mul,abs_of_nonneg (kernel_nonneg 0 n _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (kernel_zero_le_one n _)

theorem physical_first_moment {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    (∫ t : ℝ,t ∂PhysicalQuantumMeasure.measure hκ u) = fourierMomentum u := by
  let b := base u hH
  let ha : (1/2 : ℝ) < 1 := by norm_num
  let w := fun n => scaledR L n
    (mulBil hLf.out ha (jEll b)
      (mulBil hLf.out ha ((y n : ℂ) • branch hLf.out ha κ b n)
        ((y n : ℂ) • branch hLf.out ha κ b n)))
  have hw := Complex.continuous_im.continuousAt.tendsto.comp
    (nonlinear_pairing_limit (L := L) ha κ b)
  have hc : Tendsto (fun n => (κ/L)/(y n)*(floquetJ L 1 b (w n)).im) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := κ/L)).div_atTop y_atTop).mul hw
    simpa only [w,Function.comp_def,zero_mul] using hh
  have he : ∀ᶠ n in atTop,
      -(y n)^2*(EmpiricalRapidity.cauchyTransform (FullMass.Mmeas κ u) (z n)).re =
        -y n*(floquetJ L 1 b (scaledR L n b)).im +
          (κ/L)/(y n)*(floquetJ L 1 b (w n)).im := by
    filter_upwards [branch_cauchy (L := L) ha hκ b,branch_eventually hLf.out ha κ b] with n hbc hn
    rw [fieldMap_base] at hbc
    have hbc' := congrArg Complex.im hbc
    simp only [Complex.I_mul_im] at hbc'
    have hf := fixed_scaled_identity κ b n hn.2.1
    let F := modeCoefCLM hLf.out ha (jEll b)
    have hF := congrArg F hf
    change F ((y n : ℂ) • branch hLf.out ha κ b n) =
      F (scaledR L n b - (((κ/L)/(y n)^2 : ℝ) : ℂ) • w n) at hF
    rw [map_smul,map_sub,map_smul] at hF
    have hmC : (y n : ℂ)*floquetJ L 1 b (branch hLf.out ha κ b n) =
        floquetJ L 1 b (scaledR L n b)-
          (((κ/L)/(y n)^2 : ℝ) : ℂ)*floquetJ L 1 b (w n) := by
      simpa only [F,modeCoefCLM_apply,← floquetJ_eq_mode,smul_eq_mul] using hF
    have hm := congrArg Complex.im hmC
    simp only [Complex.mul_im,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul] at hm
    change (floquetJ L 1 b (branch hLf.out ha κ b n)).im =
      (EmpiricalRapidity.cauchyTransform (FullMass.Mmeas κ u) (z n)).re at hbc'
    rw [← hbc']
    have hy := (y_pos n).ne'
    field_simp [hy] at hm ⊢
    nlinarith [hm]
  have ht := ((linear_limit u hH).add hc).congr' (he.mono fun n hn => hn.symm)
  simp only [add_zero] at ht
  rw [PhysicalL2Normalization.measure_eq_Mmeas]
  exact tendsto_nhds_unique (spectral_limit hκ u hH) ht

end QuantumNLS.RootWeightedFirstR26
