import NlsGge.Birkhoff.F08Bare38
import NlsGge.Birkhoff.F07MassMoment38c
import NlsGge.Birkhoff.F05Bridge38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Ramer.CylinderSeparation
import NlsGge.Measure.ActualCountableGaussianFiniteRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal

section Window

/-- The law of an injectively indexed finite block of the countable Gaussian. -/
theorem law_block38 (q : ℤ → ℝ) {K : ℕ} (ι : Fin K → ℤ) (hι : Function.Injective ι) :
    (countableComplexGaussian q).map (fun z : ℤ → ℂ => fun k : Fin K => z (ι k)) =
      Measure.pi (fun k : Fin K => complexGaussian (q (ι k))) := by
  classical
  set U : Finset ℤ := Finset.univ.image ι with hU
  let e : Fin K ≃ U := Equiv.ofBijective (fun k => ⟨ι k, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun a b h => hι (congrArg Subtype.val h), fun ⟨u, hu⟩ => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨k, rfl⟩⟩
  have h1 := countableComplexGaussian_map_finiteRestriction q U
  have h2 := (measurePreserving_arrowCongr' (fun u : U => complexGaussian (q u.1))
    (fun k : Fin K => complexGaussian (q (ι k))) e.symm (MeasurableEquiv.refl ℂ)
    (fun u => by
      have : ι (e.symm u) = u.1 := by
        exact congrArg Subtype.val (e.apply_symm_apply u)
      simp only [this]
      exact MeasurePreserving.id _))
  have hcomp : (fun z : ℤ → ℂ => fun k : Fin K => z (ι k)) =
      (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)) ∘ U.restrict := by
    funext z k; rfl
  have hmap := Measure.map_map (μ := countableComplexGaussian q)
    (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable
    (Finset.measurable_restrict U)
  rw [hcomp, ← hmap, h1, h2.map_eq]

end Window

section WindowTail

/-- Window coordinates and tail coordinates of the countable Gaussian are independent. -/
theorem indepFun_window_tail38 (q : ℤ → ℝ) (N : ℕ) :
    IndepFun (NlsGge.Ramer.windowProj N) (fun z : ℤ → ℂ => (tailSet38 N).indicator z)
      (countableComplexGaussian q) := by
  have hind : iIndepFun (fun (n : ℤ) (z : ℤ → ℂ) => z n) (countableComplexGaussian q) :=
    iIndepFun_infinitePi (P := fun n : ℤ => complexGaussian (q n)) (X := fun n x => x)
      (fun n => measurable_id)
  have hI := hind.iIndep
  set mm : ℤ → MeasurableSpace (ℤ → ℂ) := fun n => MeasurableSpace.comap (fun z : ℤ → ℂ => z n) inferInstance
    with hmm
  have hle : ∀ n, mm n ≤ (inferInstance : MeasurableSpace (ℤ → ℂ)) :=
    fun n => (measurable_pi_apply n).comap_le
  have hdisj : Disjoint {n : ℤ | |n| ≤ (N : ℤ)} (tailSet38 N) := by
    rw [Set.disjoint_left]
    intro n hn hn'
    simp only [Set.mem_ofPred_eq, tailSet38] at hn hn'
    omega
  have hid := indep_iSup_of_disjoint hle hI hdisj
  refine Indep.symm (Indep.symm ?_)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hid ?_) ?_
  · -- window
    show MeasurableSpace.comap (NlsGge.Ramer.windowProj N)
      (MeasurableSpace.pi : MeasurableSpace (FourierPlane N)) ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    have hi : modeIndex N i ∈ {n : ℤ | |n| ≤ (N : ℤ)} := by
      have := modeIndex_bounds N i
      simp only [Set.mem_ofPred_eq]; rw [abs_le]; exact this
    exact le_iSup₂ (f := fun n (_ : n ∈ {n : ℤ | |n| ≤ (N : ℤ)}) => mm n) (modeIndex N i) hi
  · show MeasurableSpace.comap (fun z : ℤ → ℂ => (tailSet38 N).indicator z)
      (MeasurableSpace.pi : MeasurableSpace (ℤ → ℂ)) ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun n => ?_
    rw [MeasurableSpace.comap_comp]
    by_cases hn : n ∈ tailSet38 N
    · have : ((fun f : ℤ → ℂ => f n) ∘ fun z : ℤ → ℂ => (tailSet38 N).indicator z) =
          fun z => z n := by
        funext z; simp [Set.indicator, hn]
      rw [this]
      exact le_iSup₂ (f := fun n (_ : n ∈ tailSet38 N) => mm n) n hn
    · have : ((fun f : ℤ → ℂ => f n) ∘ fun z : ℤ → ℂ => (tailSet38 N).indicator z) =
          fun _ => 0 := by
        funext z; simp [Set.indicator, hn]
      rw [this, MeasurableSpace.comap_const]
      exact bot_le

end WindowTail

section Objects

variable {m : ℕ} {β : ℕ → ℝ}

/-- `P_N U` on the common Gaussian sequence space: the plane element of the low Fourier modes of
the sequence `ω ~ γ_m`.  (`ω ↦ P_N U(ω)`, `U = gaussianRealization38 m ω`.) -/
def PN38 (m N : ℕ) (ω : ℤ → ℂ) : Hm1 m :=
  planeElement38 ((m - 1 : ℕ) : ℝ) N (NlsGge.Ramer.windowProj N ω)

theorem measurable_PN38 (m N : ℕ) : Measurable (PN38 m N) :=
  (measurable_finiteElement38 _ _).comp (NlsGge.Ramer.measurable_windowProj N)

theorem PN38_coeff (m N : ℕ) (ω : ℤ → ℂ) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from PN38 m N ω) n =
      if n ∈ Finset.Icc (-(N : ℤ)) N then ω n else 0 := by
  unfold PN38 planeElement38
  rw [finiteElement_apply38 _ _ _ (modeIndex_injective N) n]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · simp only [hn, ↓reduceIte]
    obtain ⟨i, hi⟩ := modeIndex_covers N n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
    rw [← hi, finiteSeq_of_inj38 _ _ (modeIndex_injective N)]
    rfl
  · simp only [hn, ↓reduceIte]
    unfold finiteSeq38
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : modeIndex N i ≠ n := fun h => hn (h ▸ Finset.mem_Icc.2 (modeIndex_bounds N i))
    simp [hne]

variable (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
/-- `U = P_N U + Y_N` almost surely. -/
theorem ae_gr_eq_PN_add_tail38 (N : ℕ) : ∀ᵐ ω ∂(gammaM38 m β),
    gaussianRealization38 m ω = PN38 m N ω + tailRealization38 m N ω := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  filter_upwards [ae_gaussianRealization_apply38 hm hb (hβ 0 (Nat.zero_le _)) (hβ m le_rfl),
    ae_tailRealization_apply38 hm hb (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) N] with ω h1 h2
  apply Subtype.ext
  funext n
  change (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      gaussianRealization38 m ω) n =
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from PN38 m N ω) n +
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from tailRealization38 m N ω) n
  rw [h1 n, h2 n, PN38_coeff]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · have : ¬ ((N : ℤ) < |n|) := by
      rw [Finset.mem_Icc] at hn; rw [not_lt, abs_le]; exact hn
    simp [hn, this]
  · have : (N : ℤ) < |n| := by
      rw [Finset.mem_Icc] at hn; rw [lt_abs]; omega
    simp [hn, this]

include hm hβ in
/-- `P_N U` is the Hilbert truncation of `U` almost surely. -/
theorem ae_PN_eq_trunc38 : ∀ᵐ ω ∂(gammaM38 m β), ∀ N : ℕ,
    PN38 m N ω = truncSobolev38 _ N (gaussianRealization38 m ω) := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  filter_upwards [ae_gaussianRealization_apply38 hm hb (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)]
    with ω h1 N
  apply Subtype.ext
  funext n
  change (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from PN38 m N ω) n =
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      truncSobolev38 _ N (gaussianRealization38 m ω)) n
  rw [PN38_coeff, truncSobolev38_apply, h1 n]

end Objects

section CondExpV

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
/-- `V_m(U)` is integrable: polynomial bound and Gaussian moments. -/
theorem integrable_Vgr38 :
    Integrable (fun ω => vSobolev38 m β (gaussianRealization38 m ω)) (gammaM38 m β) := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  obtain ⟨C, hC0, hC⟩ := vSobolev38_bound m β
  obtain ⟨K, hK0, hKi, -⟩ := gaussianRealization_moment38 hm hb (hβ 0 (Nat.zero_le _))
    (hβ m le_rfl) (2 * m + 2)
  refine (((integrable_const (1 : ℝ)).add hKi).const_mul C).mono'
    ((continuous_vSobolev38 m β).measurable.comp measurable_gaussianRealization38).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  simpa [Real.norm_eq_abs] using hC (gaussianRealization38 m ω)

include hm hβ in
/-- **F08.02** (v2 l.826-828): `E[V_m(U) | A_N] = V_m(P_N U) + C_{m,N}(P_N U)` almost surely,
with `A_N` the σ-field of the Fourier coefficients `|n| ≤ N`, `C_{m,N}` of `C:eq:correction`. -/
theorem condExp_V_gr38 (N : ℕ) :
    (gammaM38 m β)[fun ω => vSobolev38 m β (gaussianRealization38 m ω) |
        NlsGge.Ramer.windowSigma N] =ᵐ[gammaM38 m β]
      fun ω => vSobolev38 m β (PN38 m N ω) +
        contractionCorrection38 m β N (NlsGge.Ramer.windowProj N ω) := by
  set γ := gammaM38 m β with hγ
  set X := NlsGge.Ramer.windowProj N with hX
  set Y : (ℤ → ℂ) → (ℤ → ℂ) := fun ω => (tailSet38 N).indicator ω with hY
  have hXm : Measurable X := NlsGge.Ramer.measurable_windowProj N
  have hYm : Measurable Y := measurable_indicator38 _
  have hind : IndepFun X Y γ := indepFun_window_tail38 _ N
  set Φ : FourierPlane N → (ℤ → ℂ) → ℝ := fun a b =>
    vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N a +
      seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) b) with hΦ
  have hΦm : Measurable (Function.uncurry Φ) := by
    refine (continuous_vSobolev38 m β).measurable.comp ?_
    exact ((measurable_finiteElement38 _ _).comp measurable_fst).add
      ((measurable_seqRealization38 _).comp measurable_snd)
  have hae := ae_gr_eq_PN_add_tail38 hm hβ N
  have hΦXY : (fun ω => vSobolev38 m β (gaussianRealization38 m ω)) =ᵐ[γ]
      fun ω => Φ (X ω) (Y ω) := by
    filter_upwards [hae] with ω hω
    simp only [hω, hΦ]
    rfl
  have hint : Integrable (fun ω => Φ (X ω) (Y ω)) γ :=
    (integrable_Vgr38 hm hβ).congr hΦXY
  have h1 := condExp_indep_mix38 hXm hYm hind Φ hΦm hint
  refine (condExp_congr_ae (m := NlsGge.Ramer.windowSigma N) hΦXY).trans ?_
  refine Filter.EventuallyEq.trans h1.symm ?_
  refine Filter.EventuallyEq.symm (Eventually.of_forall fun ω => ?_)
  have hmeas : Measurable (fun y : ℤ → ℂ => Φ (X ω) y) :=
    (continuous_vSobolev38 m β).measurable.comp
      (measurable_const.add (measurable_seqRealization38 _))
  have h2 : ∫ y, Φ (X ω) y ∂(γ.map Y) = ∫ s, Φ (X ω) (Y s) ∂γ :=
    integral_map hYm.aemeasurable hmeas.aestronglyMeasurable
  have hc : contractionCorrection38 m β N (X ω) =
      (∫ s, Φ (X ω) (Y s) ∂γ) - vSobolev38 m β (PN38 m N ω) := rfl
  change vSobolev38 m β (PN38 m N ω) + contractionCorrection38 m β N (X ω) =
    ∫ y, Φ (X ω) y ∂(γ.map Y)
  rw [h2, hc]
  ring

end CondExpV

section Mass

variable {m : ℕ} {β : ℕ → ℝ}

/-- `M(x) = Q_0(x) = Σ_n |x_n|²` is summable on `H^{m-1}`. -/
theorem summable_sq_coeff38 (x : Hm1 m) :
    Summable (fun n : ℤ => ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖ ^ 2) := by
  have h := weightedHilbert_hasSum (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) h.summable
  have h1 := one_le_sobolevModeWeight38 (m - 1) n
  nlinarith [sq_nonneg ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖]

/-- `Q_0(x) ≤ ‖x‖²_{H^{m-1}}`. -/
theorem mass_le_norm_sq38 (x : Hm1 m) : chargeSobolev38 m 0 x ≤ ‖x‖ ^ 2 := by
  rw [chargeSobolev38_zero m x]
  have h := weightedHilbert_hasSum (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x)
  calc ∑' n : ℤ, ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖ ^ 2
      ≤ ∑' n : ℤ, sobolevModeWeight ((m - 1 : ℕ) : ℝ) n *
        ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq_coeff38 x) h.summable
        have h1 := one_le_sobolevModeWeight38 (m - 1) n
        nlinarith [sq_nonneg ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n‖]
    _ = ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x)‖ ^ 2 := h.tsum_eq
    _ = ‖x‖ ^ 2 := rfl

theorem mass_nonneg38 (x : Hm1 m) : 0 ≤ chargeSobolev38 m 0 x := by
  rw [chargeSobolev38_zero m x]
  exact tsum_nonneg fun n => sq_nonneg _

/-- Mass of the low modes, `M(P_N U) = ‖P_N U‖²_{L²}`, on the sequence space. -/
def massN38 (N : ℕ) (ω : ℤ → ℂ) : ℝ := ‖planeL2 N (NlsGge.Ramer.windowProj N ω)‖ ^ 2

theorem measurable_massN38 (N : ℕ) : Measurable (massN38 N) := by
  unfold massN38
  simp_rw [planeL2_norm_sq]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply (modeIndex N i)).norm).pow_const 2

theorem massN38_nonneg (N : ℕ) (ω : ℤ → ℂ) : 0 ≤ massN38 N ω := sq_nonneg _

variable (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
/-- `M(P_N U) ≤ M(U)` almost surely (Fourier orthogonality: `M(U) = M(P_N U) + M(Y_N)`). -/
theorem ae_massN_le_mass38 (N : ℕ) : ∀ᵐ ω ∂(gammaM38 m β),
    massN38 N ω ≤ chargeSobolev38 m 0 (gaussianRealization38 m ω) := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  filter_upwards [ae_gaussianRealization_apply38 hm hb (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)]
    with ω h1
  rw [chargeSobolev38_zero m, massN38, planeL2_norm_sq]
  have hs := summable_sq_coeff38 (gaussianRealization38 m ω)
  simp_rw [h1] at hs ⊢
  exact plane_sum_le_tsum_E02_38 N (fun n => ‖ω n‖ ^ 2) (fun n => sq_nonneg _) hs

include hm hβ in
/-- `M(U)^m` is integrable. -/
theorem integrable_mass_pow38 :
    Integrable (fun ω => (chargeSobolev38 m 0 (gaussianRealization38 m ω)) ^ m) (gammaM38 m β) := by
  have hb := fun i (hi : i ≤ m) => (hβ i hi).le
  obtain ⟨K, hK0, hKi, -⟩ := gaussianRealization_moment38 hm hb (hβ 0 (Nat.zero_le _))
    (hβ m le_rfl) (2 * m)
  refine hKi.mono' ((((continuous_chargeSobolev38 m 0 (Nat.zero_le _)).measurable.comp
    measurable_gaussianRealization38).pow_const m).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (pow_nonneg (mass_nonneg38 _) _)]
  calc _ ≤ (‖gaussianRealization38 m ω‖ ^ 2) ^ m :=
        pow_le_pow_left₀ (mass_nonneg38 _) (mass_le_norm_sq38 _) m
    _ = _ := by rw [← pow_mul]

end Mass

end NlsGge.Birkhoff

end
