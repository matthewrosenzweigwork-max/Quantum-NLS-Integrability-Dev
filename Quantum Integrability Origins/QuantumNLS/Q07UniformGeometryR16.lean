import QuantumNLS.Q07FiniteGeometryR16
import QuantumNLS.Q07SobolevCutsR16
import QuantumNLS.Q07LogDifferentialsR16

/-! Uniform full-mass rectangle geometry for the actual Sobolev class and
one fixed full physical L2 neighborhood. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07UniformGeometryR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16
open RootSpectralInputsDischarge (dlow dlow_pos)
open ResolventNeighborhood (GammaN)
variable {L κ : ℝ} [Fact (0 < L)]

theorem physical_difference_eq_Dsrc (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    physicalDifference hκ z u = NonvanishingD.Dsrc κ L (PhysicalQuantumMeasure.measure hκ u) z := by
  unfold physicalDifference difference logarithm NonvanishingD.Dsrc RootCauchyFullBracketR8.G
  rw [RootSpectralInputsDischarge.Gfull_eq, Complex.exp_neg, div_eq_mul_inv]
  have he : Complex.I*z*(L : ℂ) = Complex.I*(L : ℂ)*z := by ring
  rw [he]

theorem gap_ae (hκ : 0 < κ) {u : L2T L} {a δ : ℝ}
    (hg : FullMass.Mmeas κ u (Ioo (a-δ) (a+δ)) = 0) :
    ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), δ ≤ |t-a| := by
  rw [← PhysicalL2Normalization.measure_eq_Mmeas hκ u] at hg
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hg] with t ht
  by_contra hn
  push Not at hn
  apply ht
  rw [abs_lt] at hn
  exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

theorem norm_discriminant_real (u : L2T L) (a : ℝ) :
    ‖L2SpatialTransfer.discriminant κ u (a : ℂ)‖ = |PhysicalL2BandGeometry.d (κ := κ) u a| := by
  have he : L2SpatialTransfer.discriminant κ u (a : ℂ) =
      ((L2SpatialTransfer.discriminant κ u (a : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [L2DiscriminantRegularity.discriminant_real]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  rfl

/-- A uniform Sobolev bound is a physical norm bound, with the declared
DEF-002 Fourier normalization retained. -/
theorem norm_le_of_class {s B : ℝ} (hs : 0 ≤ s) {u : L2T L}
    (hu : u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B) : ‖u‖ ≤ B := by
  obtain ⟨v,hv,rfl⟩ := hu
  exact (Sobolev.WField.norm_val_le (Sobolev.one_le_def002 L hs) v).trans hv

/-- The uniform geometric data for the actual rectangular contours. This
includes vacuum and nonunit profiles on one fixed full L2 neighborhood. -/
theorem uniform_contour_data (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ R d : ℝ, 1 ≤ R ∧ 0 < d ∧
      ∀ l : ℕ, l0 ≤ l → ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
        ∀ v : L2T L, ‖v-u‖ < δ → ‖v‖ < R ∧
          ∀ z ∈ GammaN (PROP017UniformN.cutSeq L l) h,
            RootCauchyJointR9.Regular κ (v,z) ∧ d ≤ ‖physicalDifference hκ z v‖ := by
  obtain ⟨η,hη,l0,hcuts⟩ := Q07SobolevCutsR16.uniform_sobolev_cuts_near (L := L) hκ hs B
  let R := max 1 (B+2)
  have hR : 1 ≤ R := le_max_left _ _
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let d := dlow L (κ*R^2) (1/L) h
  have hd : 0 < d := dlow_pos (mul_pos hκ (sq_pos_of_pos hRp)) (Fact.out : 0 < L)
    (one_div_pos.mpr (Fact.out : 0 < L)) hh
  refine ⟨min η 1, lt_min hη zero_lt_one, l0, R, d, hR, hd, ?_⟩
  intro l hl u hu v hv
  have hvη := hv.trans_le (min_le_left _ _)
  have hv1 := hv.trans_le (min_le_right _ _)
  have huB := norm_le_of_class hs.le hu
  have hvR : ‖v‖ < R := by
    have hn : ‖v‖ ≤ ‖v-u‖+‖u‖ := by
      simpa only [sub_add_cancel] using norm_add_le (v-u) u
    have hBR : B+2 ≤ R := le_max_right _ _
    linarith
  refine ⟨hvR, ?_⟩
  let a := PROP017UniformN.cutSeq L l
  obtain ⟨hc1,hb1,hg1⟩ := hcuts l hl u hu v hvη a (Or.inl rfl)
  obtain ⟨hc2,hb2,hg2⟩ := hcuts l hl u hu v hvη (-a) (Or.inr rfl)
  have mass : (PhysicalQuantumMeasure.measure hκ v).real univ ≤ R^2 := by
    rw [measureReal_def, PhysicalQuantumMeasure.measure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
    nlinarith [norm_nonneg v]
  have hΔ : Continuous (fun z => L2SpatialTransfer.discriminant κ v z) :=
    L2DiscriminantRegularity.continuous_discriminant κ v
  have hcos : ∀ z : ℂ, 0 < z.im →
      2*Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ v) z) =
        L2SpatialTransfer.discriminant κ v z :=
    fun z hz => PhysicalUnconditionalTrace.upper_cosine hκ v hz
  intro z hz
  have hlow := Q07FiniteGeometryR16.norm_Dsrc_lower (R^2) (sq_pos_of_pos hRp) mass hκ
    (Fact.out : 0 < L) (δ := 1/L) (a := a) (one_div_pos.mpr (Fact.out : 0 < L)) hh
    (gap_ae hκ hg1) (gap_ae hκ hg2) hΔ hcos
    (by rw [norm_discriminant_real]; exact hb1)
    (by rw [norm_discriminant_real]; exact hb2) hz
  refine ⟨?_, ?_⟩
  · by_cases hi : z.im = 0
    · right
      have hre : z.re = a ∨ z.re = -a := by
        rcases hz with hz | hz
        · exact hz.1
        · rcases hz.1 with hz | hz <;> linarith
      have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
      rw [he]
      rcases hre with hre | hre
      · rw [hre]
        exact hb1.trans_lt (by norm_num)
      · rw [hre]
        exact hb2.trans_lt (by norm_num)
    · exact Or.inl hi
  · rw [physical_difference_eq_Dsrc]
    exact hlow

end QuantumNLS.Q07UniformGeometryR16
