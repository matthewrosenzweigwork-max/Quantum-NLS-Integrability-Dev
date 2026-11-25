import QuantumNLS.Q07ContourDifferentiationR16
import QuantumNLS.Q07UniformDifferentialsR16

/-! Actual physical full-operator bounds and the weighted side integrands
needed to instantiate finite-interval contour differentiation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07ContourApplicationR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16 Q07ContourDifferentiationR16
open ResolventNeighborhood (GammaN)
variable {L κ : ℝ} [Fact (0 < L)]

theorem first_operator_bound (hκ : 0 < κ) {u : L2T L} {z : ℂ}
    (hp : RootCauchyJointR9.Regular κ (u,z)) {d A : ℝ} (hd : 0 < d) (hA : 0 ≤ A)
    (hD : d ≤ ‖physicalDifference hκ z u‖)
    (hS : ‖fderiv ℝ (fun v => NormalizedTransfer.productSymbol L κ v z) u‖ ≤ A) :
    ‖fderiv ℝ (logarithm hκ z) u‖ ≤ d⁻¹*A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hi : ‖(physicalDifference hκ z u)⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hd hD
  change ‖first (logarithm hκ z) u v‖ ≤ _
  rw [(physical_log_differentials hκ hp v 0).1, norm_mul]
  have hv := (fderiv ℝ (fun v => NormalizedTransfer.productSymbol L κ v z) u).le_opNorm v
  have hb : ‖first (fun v => NormalizedTransfer.productSymbol L κ v z) u v‖ ≤ A*‖v‖ :=
    hv.trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  calc
    _ ≤ d⁻¹*(A*‖v‖) := mul_le_mul hi hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Both actual full field-operator bounds, with only the printed physical
parameters as inputs. These include vacuum, nonunit and radial profiles. -/
theorem uniform_field_operators (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ A1 A2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧
      ∀ l : ℕ, l0 ≤ l → ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
        ∀ v : L2T L, ‖v-u‖ < δ → ∀ z ∈ GammaN (PROP017UniformN.cutSeq L l) h,
          RootCauchyJointR9.Regular κ (v,z) ∧
          ‖fderiv ℝ (logarithm hκ z) v‖ ≤ A1 ∧
          ‖fderiv ℝ (fderiv ℝ (logarithm hκ z)) v‖ ≤ A2 := by
  obtain ⟨δg,hg,lg,R,d,hR,hd,hgeo⟩ := Q07UniformGeometryR16.uniform_contour_data (L := L) hκ hs B hh
  obtain ⟨δh,hδh,lh,C,hC,hH⟩ := Q07UniformDifferentialsR16.uniform_log_hessians (L := L) hκ hs B hh
  obtain ⟨C1,_,h1,_,hT⟩ := Q07NormalSeriesR15.transfer_uniform_differentials (L := L) κ hR hh.le
  refine ⟨min δg δh,lt_min hg hδh,max lg lh,d⁻¹*C1,C,by positivity,hC,?_⟩
  intro l hl u hu v hv z hz
  have hlg := (le_max_left lg lh).trans hl
  have hlh := (le_max_right lg lh).trans hl
  obtain ⟨hvR,hGe⟩ := hgeo l hlg u hu v (hv.trans_le (min_le_left _ _))
  obtain ⟨hp,hD⟩ := hGe z hz
  have hi := NonvanishingD.GammaN_im_abs hh.le hz
  have ht := (hT z (by linarith [neg_le_abs z.im]) v (mem_ball_zero_iff.mpr hvR)).1
  refine ⟨hp,first_operator_bound hκ hp hd h1 hD ht,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg w))
  intro q
  have hlog : ContDiffAt ℝ 2 (logarithm hκ z) v := (logarithm_analytic hκ hp).contDiffAt
  rw [← Q07LogBoundsR16.second_eq hlog q w]
  have hb := (hH l hlh u hu v (hv.trans_le (min_le_right _ _)) z hz).2 q w
  nlinarith

/-- Canonical first partial derivative of a weighted contour-side integrand. -/
theorem weighted_first (hκ : 0 < κ) (r : ℕ) (γ : ℝ → ℂ) {u : L2T L} {t : ℝ}
    (hp : RootCauchyJointR9.Regular κ (u,γ t)) :
    fieldPartial (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1) (u,t) =
      (γ t)^r • fderiv ℝ (logarithm hκ (γ t)) u :=
  ((logarithm_analytic hκ hp).differentiableAt.hasFDerivAt.const_mul ((γ t)^r)).fderiv

/-- Its canonical second partial derivative, derived on the open regular set. -/
theorem weighted_second (hκ : 0 < κ) (r : ℕ) (γ : ℝ → ℂ) {u : L2T L} {t : ℝ}
    (hp : RootCauchyJointR9.Regular κ (u,γ t)) :
    fieldPartial (fieldPartial (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1)) (u,t) =
      (γ t)^r • fderiv ℝ (fderiv ℝ (logarithm hκ (γ t))) u := by
  have ho := (RootCauchyJointR9.isOpen_regular κ).preimage
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : L2T L => γ t)))
  have he : (fun v : L2T L => fieldPartial
      (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1) (v,t)) =ᶠ[𝓝 u]
      (fun v => (γ t)^r • fderiv ℝ (logarithm hκ (γ t)) v) := by
    filter_upwards [ho.mem_nhds hp] with v hv
    exact weighted_first hκ r γ hv
  have hd : DifferentiableAt ℝ (fderiv ℝ (logarithm hκ (γ t))) u :=
    (((logarithm_analytic hκ hp).contDiffAt (n := 2)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  change fderiv ℝ _ u = _
  rw [he.fderiv_eq]
  exact (hd.hasFDerivAt.const_smul ((γ t)^r)).fderiv

/-- Actual analytic weighted side functions satisfy the finite-interval
interchange theorem once the already proved common field bounds are applied. -/
theorem weighted_side (hκ : 0 < κ) (r : ℕ) (γ : ℝ → ℂ) {U : Set (L2T L)}
    (hU : IsOpen U) {a b Z A1 A2 : ℝ} (hab : a ≤ b) (hZ : 0 ≤ Z)
    (hγ : ∀ t ∈ Icc a b, AnalyticAt ℝ γ t)
    (hγZ : ∀ t ∈ Icc a b, ‖γ t‖ ≤ Z)
    (hreg : ∀ u ∈ U, ∀ t ∈ Icc a b, RootCauchyJointR9.Regular κ (u,γ t))
    (hB1 : ∀ u ∈ U, ∀ t ∈ Icc a b, ‖fderiv ℝ (logarithm hκ (γ t)) u‖ ≤ A1)
    (hB2 : ∀ u ∈ U, ∀ t ∈ Icc a b, ‖fderiv ℝ (fderiv ℝ (logarithm hκ (γ t))) u‖ ≤ A2)
    {u : L2T L} (hu : u ∈ U) :
    HasFDerivAt (fun v => ∫ t in a..b, γ t^r*logarithm hκ (γ t) v)
      (∫ t in a..b, fieldPartial
        (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1) (u,t)) u ∧
    HasFDerivAt (fderiv ℝ (fun v => ∫ t in a..b, γ t^r*logarithm hκ (γ t) v))
      (∫ t in a..b, fieldPartial (fieldPartial
        (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1)) (u,t)) u := by
  have hf : ∀ v ∈ U, ∀ t ∈ Icc a b,
      AnalyticAt ℝ (fun p : L2T L × ℝ => γ p.2^r*logarithm hκ (γ p.2) p.1) (v,t) := by
    intro v hv t ht
    have hw : AnalyticAt ℝ (fun p : L2T L × ℝ => γ p.2) (v,t) :=
      (hγ t ht).comp analyticAt_snd
    have hm : AnalyticAt ℝ (fun p : L2T L × ℝ => (p.1,γ p.2)) (v,t) := analyticAt_fst.prod hw
    have hlog : AnalyticAt ℝ (fun p : L2T L × ℝ => logarithm hκ (γ p.2) p.1) (v,t) := by
      exact AnalyticAt.comp (g := fun p : L2T L × ℂ => logarithm hκ p.2 p.1)
        (f := fun p : L2T L × ℝ => (p.1,γ p.2)) (x := (v,t))
        (analytic_joint_logarithm hκ (hreg v hv t ht)) hm
    exact (hw.pow r).mul hlog
  apply second_interval hU hab hf (C1 := Z^r*A1) (C2 := Z^r*A2) _ _ hu
  · intro v hv t ht
    rw [weighted_first hκ r γ (hreg v hv t ht), norm_smul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hγZ t ht) r)
      (hB1 v hv t ht) (norm_nonneg _) (pow_nonneg hZ r)
  · intro v hv t ht
    rw [weighted_second hκ r γ (hreg v hv t ht), norm_smul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hγZ t ht) r)
      (hB2 v hv t ht) (norm_nonneg _) (pow_nonneg hZ r)

end QuantumNLS.Q07ContourApplicationR16
