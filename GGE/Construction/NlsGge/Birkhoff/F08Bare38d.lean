import NlsGge.Birkhoff.F08Bare38c

/-! # F08 (v2 `C:thm:bare`), file d: the bare Fourier-plane objects

`E_m` on the Fourier plane `F_N`, the partition function `𝒵_{m,N}`, the bare measure `ν_{m,N}` of
`C:eq:bare` as a measure on `H^{m-1}`, and their expression through the Gaussian `γ_m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations
open scoped ENNReal

section Def

/-- `E_m(v) = Σ_{j≤m} β_j Q_{2j}(v)` for `v ∈ F_N` (Fourier coordinates `z`, `û(n) = z_i`,
`n = modeIndex N i`), with the charges `Q_{2j}` (`chargeSobolev38`, the continuous extension of the
local = spectral charge) evaluated at the trigonometric polynomial `v ∈ H^m`. -/
def EmPlane38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) : ℝ :=
  energySobolev38 m β (planeElement38 (m : ℝ) N z)

/-- `𝒵_{m,N} = ∫_{F_N} e^{-E_m(v)} ∏_{|n|≤N} d²û(n)`. -/
def ZcalBare38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∫ z, Real.exp (-(EmPlane38 m β N z)) ∂(finiteComplexVolume (Fin (2 * N + 1)))

/-- The bare Fourier measure `ν_{m,N}` of `C:eq:bare`, a probability measure on `H^{m-1}`
supported on the Fourier plane `F_N`: `dν = 𝒵⁻¹ e^{-E_m(v)} ∏ d²û(n)`. -/
def nuBare38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measure (Hm1 m) :=
  ((finiteComplexVolume (Fin (2 * N + 1))).withDensity
    (fun z => ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N))).map
    (planeElement38 ((m - 1 : ℕ) : ℝ) N)

/-- The Gaussian rates `a_{m,n}` on the Fourier plane. -/
def windowRate38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  finiteHierarchyRate38 m β (modeIndex N i)

/-- `∏_{|n|≤N} π/a_{m,n}`. -/
def gaussConst38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ i : Fin (2 * N + 1), Real.pi / windowRate38 m β N i

end Def

section Basic

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include hm hβ in
theorem windowRate_pos38 (N : ℕ) (i : Fin (2 * N + 1)) : 0 < windowRate38 m β N i :=
  rate_pos38 m β (by omega) (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) _

include hm hβ in
theorem gaussConst_pos38 (N : ℕ) : 0 < gaussConst38 m β N :=
  Finset.prod_pos fun i _ => div_pos Real.pi_pos (windowRate_pos38 hm hβ N i)

/-- Law of the low Fourier coordinates of `γ_m`. -/
theorem law_window38 (N : ℕ) :
    (gammaM38 m β).map (NlsGge.Ramer.windowProj N) =
      finiteComplexGaussian (windowRate38 m β N) := by
  have := law_block38 (finiteHierarchyRate38 m β) (modeIndex N) (modeIndex_injective N)
  exact this

/-- The coefficients of the plane element are the plane coordinates. -/
theorem planeElement_coeff38 (r : ℝ) (N : ℕ) (z : FourierPlane N) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from planeElement38 r N z) n =
      finiteSeq38 (modeIndex N) z n :=
  finiteElement_apply38 r _ _ (modeIndex_injective N) n

theorem tsum_plane38 (N : ℕ) (g : ℤ → ℝ) (hg : ∀ n, n ∉ Finset.univ.image (modeIndex N) → g n = 0) :
    ∑' n, g n = ∑ i : Fin (2 * N + 1), g (modeIndex N i) := by
  rw [tsum_eq_sum (s := Finset.univ.image (modeIndex N)) (fun n hn => hg n hn)]
  rw [Finset.sum_image (fun a _ b _ h => modeIndex_injective N h)]

theorem finiteSeq_zero_off38 (N : ℕ) (z : FourierPlane N) (n : ℤ)
    (hn : n ∉ Finset.univ.image (modeIndex N)) : finiteSeq38 (modeIndex N) z n = 0 := by
  unfold finiteSeq38
  refine Finset.sum_eq_zero fun k _ => ?_
  have hne : modeIndex N k ≠ n := fun h => hn (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h⟩)
  simp [hne]

include hm in
/-- On a Fourier plane, `E_m(v) = Σ_{|n|≤N} a_{m,n}|û(n)|² + V_m(v)` (`B:eq:Vm`). -/
theorem EmPlane_eq38 (N : ℕ) (z : FourierPlane N) :
    EmPlane38 m β N z = ∑ i, windowRate38 m β N i * ‖z i‖ ^ 2 +
      vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z) := by
  have hyy : ∀ n, (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from
      planeElement38 (m : ℝ) N z) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
        planeElement38 ((m - 1 : ℕ) : ℝ) N z) n := fun n => by
    rw [planeElement_coeff38, planeElement_coeff38]
  have h := energyIdentity_fourier38 m hm β (planeElement38 (m : ℝ) N z)
    (planeElement38 ((m - 1 : ℕ) : ℝ) N z) hyy
  unfold EmPlane38 vSobolev38
  rw [h]
  congr 1
  rw [tsum_plane38 N (fun n => finiteHierarchyRate38 m β n *
    ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from planeElement38 (m : ℝ) N z) n‖ ^ 2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [planeElement_coeff38, finiteSeq_of_inj38 _ _ (modeIndex_injective N)]
    rfl
  · intro n hn
    rw [planeElement_coeff38, finiteSeq_zero_off38 N z n hn]
    simp

end Basic

section Coercive

/-- `Q_{2j} ≥ 0` on a Fourier plane element: the plane charge is the nonnegative spectral charge. -/
theorem chargeSobolev38_plane_nonneg (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m) (N : ℕ)
    (z : FourierPlane N) :
    0 ≤ chargeSobolev38 m j (planeElement38 ((m - 1 : ℕ) : ℝ) N z) := by
  rw [chargeSobolev38_smooth m j hm hj (planeReal N z) (planeReal_smooth38 N z)
    (planeReal_periodic N z) _ (planeElement_hsource38 _ N z)]
  exact localCharge38_plane_nonneg N z j


variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- `Q_0` of a plane element is the sum of the squared plane coordinates. -/
theorem mass_plane38 (N : ℕ) (z : FourierPlane N) :
    chargeSobolev38 (m + 1) 0 (planeElement38 (m : ℝ) N z) = ∑ i, ‖z i‖ ^ 2 := by
  rw [chargeSobolev38_zero (m + 1)]
  rw [tsum_plane38 N (fun n => ‖(show WeightedHilbert (sobolevModeWeight (((m + 1 - 1 : ℕ) : ℝ))) from
    planeElement38 (m : ℝ) N z) n‖ ^ 2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [planeElement_coeff38, finiteSeq_of_inj38 _ _ (modeIndex_injective N)]
  · intro n hn
    rw [planeElement_coeff38, finiteSeq_zero_off38 N z n hn]
    simp

include hm hβ in
/-- `E_m ≥ β_0 Q_0` on Fourier planes (v2 `C:eq:bare`: "`E_m ≥ β_0 Q_0` ...").  Every `Q_{2j}` is
nonnegative and `Q_0 = Σ|û(n)|²`. -/
theorem EmPlane_ge38 (N : ℕ) (z : FourierPlane N) :
    β 0 * ∑ i, ‖z i‖ ^ 2 ≤ EmPlane38 m β N z := by
  unfold EmPlane38 energySobolev38
  have hnn : ∀ j ∈ Finset.range (m + 1),
      0 ≤ β j * chargeSobolev38 (m + 1) j (planeElement38 (m : ℝ) N z) := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact mul_nonneg (hβ j hj').le (chargeSobolev38_plane_nonneg (m + 1) j (by omega) (by omega) N z)
  have := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.succ_pos m))
  rw [mass_plane38 N z] at this
  exact this

include hm hβ in
theorem measurable_EmPlane38 (N : ℕ) : Measurable (EmPlane38 m β N) := by
  have : EmPlane38 m β N = fun z => ∑ i, windowRate38 m β N i * ‖z i‖ ^ 2 +
      vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z) := funext (EmPlane_eq38 hm N)
  rw [this]
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_)
    ((continuous_vSobolev38 m β).measurable.comp (measurable_finiteElement38 _ _))
  exact measurable_const.mul ((measurable_pi_apply i).norm.pow_const 2)

include hm hβ in
/-- The integrand of `𝒵_{m,N}` is integrable (dominated by `e^{-β_0 M}`). -/
theorem integrable_expEm38 (N : ℕ) :
    Integrable (fun z => Real.exp (-(EmPlane38 m β N z))) (finiteComplexVolume (Fin (2 * N + 1))) := by
  have hker := integrable_finiteComplexGaussianKernel (ι := Fin (2 * N + 1)) (fun _ => β 0)
    (fun _ => hβ 0 (Nat.zero_le _))
  refine hker.mono' ((Real.measurable_exp.comp (measurable_EmPlane38 hm hβ N).neg).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := EmPlane_ge38 hm hβ N z
  have h2 : ∏ i : Fin (2 * N + 1), Real.exp (-β 0 * ‖z i‖ ^ 2) =
      Real.exp (-(β 0 * ∑ i, ‖z i‖ ^ 2)) := by
    rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  exact Real.exp_le_exp.2 (by linarith)

end Coercive

section GaussRep

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- The Gaussian density `∏_{|n|≤N} (a_{m,n}/π) e^{-a_{m,n}|z_n|²}` on the plane. -/
def gaussDensPlane38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) : ℝ :=
  ∏ i, (windowRate38 m β N i / Real.pi) * Real.exp (-(windowRate38 m β N i) * ‖z i‖ ^ 2)

include hm hβ in
theorem expEm_eq38 (N : ℕ) (z : FourierPlane N) :
    Real.exp (-(EmPlane38 m β N z)) = gaussConst38 m β N *
      (gaussDensPlane38 m β N z *
        Real.exp (-(vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z)))) := by
  rw [EmPlane_eq38 hm N z, neg_add, Real.exp_add, gaussDensPlane38]
  have e2 : Real.exp (-∑ i, windowRate38 m β N i * ‖z i‖ ^ 2) =
      ∏ i, Real.exp (-(windowRate38 m β N i) * ‖z i‖ ^ 2) := by
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have e3 : gaussConst38 m β N * ∏ i, (windowRate38 m β N i / Real.pi) *
      Real.exp (-(windowRate38 m β N i) * ‖z i‖ ^ 2) =
      ∏ i, Real.exp (-(windowRate38 m β N i) * ‖z i‖ ^ 2) := by
    rw [gaussConst38, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have := (windowRate_pos38 hm hβ N i).ne'
    field_simp
  rw [e2, ← mul_assoc, e3]

include hm hβ in
theorem integral_gauss_density38 (N : ℕ) (g : FourierPlane N → ℝ) :
    ∫ z, g z ∂(finiteComplexGaussian (windowRate38 m β N)) =
      ∫ z, gaussDensPlane38 m β N z * g z ∂(finiteComplexVolume (Fin (2 * N + 1))) := by
  have hmeas : Measurable (fun z : FourierPlane N => ENNReal.ofReal (gaussDensPlane38 m β N z)) :=
    (measurable_finiteGaussianPDF (windowRate38 m β N)).ennreal_ofReal
  have hd : finiteComplexGaussian (windowRate38 m β N) =
      (finiteComplexVolume (Fin (2 * N + 1))).withDensity
        (fun z => ENNReal.ofReal (gaussDensPlane38 m β N z)) :=
    finiteComplexGaussian_density (windowRate38 m β N) (windowRate_pos38 hm hβ N)
  rw [hd, integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (show 0 ≤ gaussDensPlane38 m β N z from
    Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg _
      (windowRate_pos38 hm hβ N i) (z i)))]

include hm hβ in
/-- Transfer of a bare-plane integral to the Gaussian sequence space:
`∫_{F_N} g e^{-E_m} d²z = ∏(π/a) · E[g(P_N U) e^{-V_m(P_N U)}]`. -/
theorem integral_bare38 (N : ℕ) (g : FourierPlane N → ℝ) (hg : Measurable g) :
    ∫ z, g z * Real.exp (-(EmPlane38 m β N z)) ∂(finiteComplexVolume (Fin (2 * N + 1))) =
      gaussConst38 m β N * ∫ ω, g (NlsGge.Ramer.windowProj N ω) *
        Real.exp (-(vSobolev38 m β (PN38 m N ω))) ∂(gammaM38 m β) := by
  set h : FourierPlane N → ℝ := fun z =>
    g z * Real.exp (-(vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z))) with hh
  have hhm : Measurable h :=
    hg.mul (Real.measurable_exp.comp ((continuous_vSobolev38 m β).measurable.comp
      (measurable_finiteElement38 _ _)).neg)
  have h1 : ∀ z : FourierPlane N, g z * Real.exp (-(EmPlane38 m β N z)) =
      gaussConst38 m β N * (gaussDensPlane38 m β N z * h z) := by
    intro z
    rw [expEm_eq38 hm hβ N z, hh]
    ring
  simp_rw [h1]
  rw [integral_const_mul, ← integral_gauss_density38 hm hβ N h, ← law_window38 (m := m) (β := β) N,
    integral_map (NlsGge.Ramer.measurable_windowProj N).aemeasurable hhm.aestronglyMeasurable]
  rfl

end GaussRep

section Weights

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

/-- The bare weight `e^{-V_m(P_N U)}` on the Gaussian sequence space. -/
def weightN38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (ω : ℤ → ℂ) : ℝ :=
  Real.exp (-(vSobolev38 m β (PN38 m N ω)))

/-- The limit weight `e^{-V_m(U)}`, `U = gaussianRealization38 m ω ~ γ_m^F`. -/
def weightInf38 (m : ℕ) (β : ℕ → ℝ) (ω : ℤ → ℂ) : ℝ :=
  Real.exp (-(vSobolev38 m β (gaussianRealization38 m ω)))

theorem measurable_weightN38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measurable (weightN38 m β N) :=
  Real.measurable_exp.comp ((continuous_vSobolev38 m β).measurable.comp (measurable_PN38 m N)).neg

theorem measurable_weightInf38 (m : ℕ) (β : ℕ → ℝ) : Measurable (weightInf38 m β) :=
  Real.measurable_exp.comp
    ((continuous_vSobolev38 m β).measurable.comp measurable_gaussianRealization38).neg

theorem weightN38_pos (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (ω : ℤ → ℂ) : 0 < weightN38 m β N ω :=
  Real.exp_pos _

include hm hβ in
/-- Each bare weight is `γ_m`-integrable: `e^{-V_m(v)} = e^{-E_m(v)} e^{Σ a|û|²}` and `E_m ≥ β_0 Q_0`. -/
theorem integrable_weightN38 (N : ℕ) : Integrable (weightN38 m β N) (gammaM38 m β) := by
  set f : FourierPlane N → ℝ := fun z =>
    Real.exp (-(vSobolev38 m β (planeElement38 ((m - 1 : ℕ) : ℝ) N z))) with hf
  have hfm : Measurable f :=
    Real.measurable_exp.comp ((continuous_vSobolev38 m β).measurable.comp
      (measurable_finiteElement38 _ _)).neg
  have hdens : Measurable (fun z : FourierPlane N => ENNReal.ofReal (gaussDensPlane38 m β N z)) :=
    (measurable_finiteGaussianPDF (windowRate38 m β N)).ennreal_ofReal
  have hd : finiteComplexGaussian (windowRate38 m β N) =
      (finiteComplexVolume (Fin (2 * N + 1))).withDensity
        (fun z => ENNReal.ofReal (gaussDensPlane38 m β N z)) :=
    finiteComplexGaussian_density (windowRate38 m β N) (windowRate_pos38 hm hβ N)
  have h1 : Integrable f (finiteComplexGaussian (windowRate38 m β N)) := by
    rw [hd, integrable_withDensity_iff_integrable_smul' hdens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hc := (integrable_expEm38 hm hβ N).const_mul (gaussConst38 m β N)⁻¹
    refine hc.congr (Eventually.of_forall fun z => ?_)
    have hpos := gaussConst_pos38 hm hβ N
    have hdn : 0 ≤ gaussDensPlane38 m β N z :=
      Finset.prod_nonneg (fun i _ => normalizedGaussianKernel_nonneg _
        (windowRate_pos38 hm hβ N i) (z i))
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal hdn, expEm_eq38 hm hβ N z, hf]
    field_simp
  rw [← law_window38 (m := m) (β := β) N] at h1
  exact (integrable_map_measure hfm.aestronglyMeasurable
    (NlsGge.Ramer.measurable_windowProj N).aemeasurable).1 h1

include hm hβ in
theorem ZcalBare_eq38 (N : ℕ) :
    ZcalBare38 m β N = gaussConst38 m β N * ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) := by
  have := integral_bare38 hm hβ N (fun _ => 1) measurable_const
  simpa [ZcalBare38, weightN38, PN38] using this

include hm hβ in
theorem integral_weightN_pos38 (N : ℕ) : 0 < ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) :=
  integral_exp_pos (f := fun ω => -(vSobolev38 m β (PN38 m N ω))) (integrable_weightN38 hm hβ N)

include hm hβ in
theorem ZcalBare_pos38 (N : ℕ) : 0 < ZcalBare38 m β N := by
  rw [ZcalBare_eq38 hm hβ N]
  exact mul_pos (gaussConst_pos38 hm hβ N) (integral_weightN_pos38 hm hβ N)

include hm hβ in
/-- The relative normalizer `𝒵_{m,N}/∏(π/a_{m,n}) = E[e^{-V_m(P_N U)}]`. -/
theorem ZcalBare_rel38 (N : ℕ) :
    ZcalBare38 m β N / gaussConst38 m β N = ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) := by
  rw [ZcalBare_eq38 hm hβ N]
  have := (gaussConst_pos38 hm hβ N).ne'
  field_simp

include hm hβ in
theorem isProbabilityMeasure_nuBare38 (N : ℕ) : IsProbabilityMeasure (nuBare38 m β N) := by
  have hZ := ZcalBare_pos38 hm hβ N
  have hint := (integrable_expEm38 hm hβ N).div_const (ZcalBare38 m β N)
  have hpe : Measurable (planeElement38 ((m - 1 : ℕ) : ℝ) N) := measurable_finiteElement38 _ _
  refine ⟨?_⟩
  unfold nuBare38
  rw [Measure.map_apply hpe MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hZ.le)]
  have : ∫ z, Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N
      ∂(finiteComplexVolume (Fin (2 * N + 1))) = 1 := by
    rw [integral_div]
    exact div_self hZ.ne'
  rw [this]
  simp

include hm hβ in
/-- `∫ F dν_{m,N} = E[F(P_N U) e^{-V_m(P_N U)}] / E[e^{-V_m(P_N U)}]`. -/
theorem integral_nuBare38 (N : ℕ) (F : Hm1 m → ℝ) (hF : Measurable F) :
    ∫ u, F u ∂(nuBare38 m β N) =
      (∫ ω, F (PN38 m N ω) * weightN38 m β N ω ∂(gammaM38 m β)) /
        ∫ ω, weightN38 m β N ω ∂(gammaM38 m β) := by
  have hZ := ZcalBare_pos38 hm hβ N
  have hpe : Measurable (planeElement38 ((m - 1 : ℕ) : ℝ) N) := measurable_finiteElement38 _ _
  have hdens : Measurable (fun z : FourierPlane N =>
      ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N)) :=
    (Real.measurable_exp.comp (measurable_EmPlane38 hm hβ N).neg |>.div_const _).ennreal_ofReal
  unfold nuBare38
  rw [integral_map hpe.aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∀ z : FourierPlane N,
      (ENNReal.ofReal (Real.exp (-(EmPlane38 m β N z)) / ZcalBare38 m β N)).toReal •
        F (planeElement38 ((m - 1 : ℕ) : ℝ) N z) =
      (ZcalBare38 m β N)⁻¹ * (F (planeElement38 ((m - 1 : ℕ) : ℝ) N z) *
        Real.exp (-(EmPlane38 m β N z))) := by
    intro z
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul]
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, integral_bare38 hm hβ N (fun z => F (planeElement38 ((m - 1 : ℕ) : ℝ) N z))
    (hF.comp hpe), ZcalBare_eq38 hm hβ N]
  have := (gaussConst_pos38 hm hβ N).ne'
  have h2 := (integral_weightN_pos38 hm hβ N).ne'
  unfold weightN38 PN38 at *
  field_simp

end Weights

end NlsGge.Birkhoff

end
