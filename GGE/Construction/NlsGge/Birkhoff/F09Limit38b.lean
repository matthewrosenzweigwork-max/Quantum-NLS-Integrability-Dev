import NlsGge.Birkhoff.F09Limit38

/-! # NEW-F09, file 2: transfer between the Fourier plane and `E_s`, and the `h²` norm of `P_N x`

`B`-free. Source: `paper/v2.tex` l.1695-1700 (`F:eq:weights`: `f_N^F(U) = f_N(𝓕U)`), l.1774-1781.

* `integral_transfer38`: `∫_{E_s} φ(P_N x as plane point) dγ_W = ∫_{plane} φ dγ_N`;
* `norm_sq_eToSob2_projE38`: `‖P_N x‖²_{h²} = planeH2NormSq38 N (plane coordinates of P_N x)`;
* `sectionE38`: a continuous section of the plane coordinates, so a test function that is continuous on
  `𝓕⁻¹E_s` is continuous on the plane;
* `integral_nuWN38_Es`: `∫ G dν_{W,N} = Z_N⁻¹ ∫_{E_s} G(𝓕⁻¹P_N x) f_N(x) dγ_W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

theorem measurable_planeOfSeq38 (N : ℕ) : Measurable (planeOfSeq38 N) := by
  unfold planeOfSeq38 reflectPlane
  exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).neg.comp
    (measurable_pi_iff.2 fun j => measurable_pi_apply _)

theorem sum_plane_even_eq38 (N : ℕ) (w : ℤ → ℝ) (hw : ∀ n, w (-n) = w n) (x : ℤ → ℂ) :
    ∑ i : Fin (2 * N + 1), w (modeIndex N i) * ‖planeOfSeq38 N x i‖ ^ 2 =
      ∑ n ∈ symmetricModes N, w n * ‖x n‖ ^ 2 := by
  rw [symmetricModes_eq_image, Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
  rw [← Equiv.sum_comp (reflectMode_involutive N).toPerm
    (fun i => w (modeIndex N i) * ‖x (modeIndex N i)‖ ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [planeOfSeq38, reflectPlane, norm_neg, Function.Involutive.coe_toPerm]
  rw [← hw (modeIndex N i), ← modeIndex_reflect]

section Transfer

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- **Transfer.** Integrals over `E_s` of functions of the plane coordinates of `P_N x` equal integrals over the
Fourier-plane Gaussian `γ_N` (`(planeOfSeq ∘ coordE)_# γ_W = γ_N`). -/
theorem integral_transfer38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) (φ : FourierPlane N → ℝ)
    (hφ : AEStronglyMeasurable φ (fullWeightFourierGaussian N c.val)) :
    ∫ x, φ (planeOfSeq38 N (coordE c s x)) ∂(fullWeightedSequenceGaussian c s) =
      ∫ z, φ z ∂(fullWeightFourierGaussian N c.val) := by
  have hm := measurable_planeOfSeq38 N
  have hmap := map_planeOfSeq38 c N
  have hf : AEStronglyMeasurable (fun ζ => φ (planeOfSeq38 N ζ)) (fullWeightSequenceGaussian c.val) := by
    rw [← hmap] at hφ
    exact hφ.comp_aemeasurable hm.aemeasurable
  rw [integral_comp_coordE c s hs hf]
  conv_rhs => rw [← hmap]
  rw [integral_map hm.aemeasurable (by rw [hmap]; exact hφ)]

theorem sobolevModeWeight_two38 (n : ℤ) :
    sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n = (1 + (n : ℝ) ^ 2) ^ 2 := by
  unfold sobolevModeWeight japaneseBracket
  have h : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by positivity
  rw [show (2 * (((1 + 1 : ℕ)) : ℝ)) = ((4 : ℕ) : ℝ) by norm_num]
  change Real.sqrt (1 + (n : ℝ) ^ 2) ^ (((4 : ℕ) : ℝ)) = _
  rw [Real.rpow_natCast, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt h]

/-- `‖P_N x‖²_{h²}` equals `planeH2NormSq38` of the plane coordinates of `P_N x`. -/
theorem norm_sq_eToSob2_projE38 (N : ℕ) (x : ECarrier38 c s) :
    ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (projE38 c s N x)‖ ^ 2 =
      planeH2NormSq38 N (planeOfSeq38 N (coordE c s x)) := by
  have h := carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ)
    (eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (projE38 c s N x))
  simp only [carrierCoe_eToSob38, eCoe38_projE38] at h
  set f : ℤ → ℝ := fun n => sobolevModeWeight (((1 + 1 : ℕ)) : ℝ) n *
      ‖if n ∈ symmetricModes N then eCoe38 c s x n else 0‖ ^ 2 with hf
  have h2 : HasSum f (∑ n ∈ symmetricModes N, f n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hf, hn])
  rw [h.unique h2]
  unfold planeH2NormSq38
  have := sum_plane_even_eq38 N (fun n => (1 + (n : ℝ) ^ 2) ^ 2) (fun n => by simp) (coordE c s x)
  beta_reduce at this
  rw [this]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [hf, hn, ite_true, sobolevModeWeight_two38]
  rfl

/-- A continuous section of the plane coordinates: `z ↦ ` the head element of `E_s` whose plane coordinates
(`planeOfSeq38 N ∘ coordE`) are `z`. -/
def sectionE38 (N : ℕ) (z : FourierPlane N) : ECarrier38 c s :=
  headToE c s N ((actualCMHeadCoord c N).symm (reflectPlane N z))

theorem continuous_sectionE38 (N : ℕ) : Continuous (sectionE38 c s N) := by
  unfold sectionE38
  have h1 : Continuous (fun z : FourierPlane N => (actualCMHeadCoord c N).symm (reflectPlane N z)) := by
    refine (LinearMap.continuous_of_finiteDimensional
      ((actualCMHeadCoord c N).symm.toLinearMap)).comp ?_
    unfold reflectPlane
    exact continuous_pi fun i => (continuous_apply _).neg
  exact (headToE c s N).continuous.comp h1

theorem planeOfSeq38_coordE_sectionE38 (N : ℕ) (z : FourierPlane N) :
    planeOfSeq38 N (coordE c s (sectionE38 c s N z)) = z := by
  have h : ∀ i, coordE c s (sectionE38 c s N z) (modeIndex N i) = reflectPlane N z i := by
    intro i
    change cmCoord (((actualCMHeadCoord c N).symm (reflectPlane N z) : actualCMHead c N) : ActualCM c)
      (modeIndex N i) = _
    exact (actualCMHeadCoord_apply c N _ i).symm.trans (by
      rw [LinearEquiv.apply_symm_apply])
  unfold planeOfSeq38
  have : (fun i => coordE c s (sectionE38 c s N z) (modeIndex N i)) = reflectPlane N z :=
    funext h
  rw [this]
  exact reflectPlane_involutive N z

theorem planeL2_eq_physOfE_projE_sectionE38 (N : ℕ) (z : FourierPlane N) :
    planeL2 N z = physOfE38 c s (projE38 c s N (sectionE38 c s N z)) := by
  have h := physOfE38_projE38_W07 c s N (sectionE38 c s N z)
  rw [planeOfSeq38_coordE_sectionE38] at h
  exact h.symm

/-- A test function continuous on `𝓕⁻¹E_s` is continuous on the Fourier plane. -/
theorem continuous_comp_planeL2_of_cont38 (G : PhysicalL2 → ℝ)
    (hG : Continuous (fun y : ECarrier38 c s => G (physOfE38 c s y))) (N : ℕ) :
    Continuous (fun z : FourierPlane N => G (planeL2 N z)) := by
  have : (fun z : FourierPlane N => G (planeL2 N z)) =
      (fun y : ECarrier38 c s => G (physOfE38 c s y)) ∘ (projE38 c s N) ∘ (sectionE38 c s N) :=
    funext fun z => by simp only [Function.comp, planeL2_eq_physOfE_projE_sectionE38 c s N z]
  rw [this]
  exact hG.comp ((projE38 c s N).continuous.comp (continuous_sectionE38 c s N))

/-- **Bridge `ν_{W,N} ↔ γ_W` on `E_s`.** -/
theorem integral_nuWN38_Es (hs : (1 : ℝ) / 2 < s) (N : ℕ) (G : PhysicalL2 → ℝ)
    (hG : Measurable (fun z : FourierPlane N => G (planeL2 N z))) :
    ∫ u, G u ∂(nuWN38 c N) = (1 / relativePartition38 c N) *
      ∫ x, G (physOfE38 c s (projE38 c s N x)) * fN38 c s N x ∂(fullWeightedSequenceGaussian c s) := by
  rw [integral_nuWN38_gauss c N G hG.aestronglyMeasurable]
  congr 1
  have hf : Measurable (fFourier38 c N) := by
    unfold fFourier38
    have := continuous_fullEnergy38 c N
    fun_prop
  rw [← integral_transfer38 c s hs N (fun z => G (planeL2 N z) * fFourier38 c N z)
    (hG.mul hf).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [physOfE38_projE38_W07, fN38_eq_fNseq]
  rfl

end Transfer

end NlsGge.Birkhoff
end
