import QuantumNLS.Prop026Mixed
import QuantumNLS.DEF014Round5

/-! Physical binding of the fixed-action datum. All inherited modules are read-only.
The cut set is the actual open bands, not an empty or supplied set. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.Prop026Bound
open PhysicalTensor (L2T)
open IndexedScalarMeasure IndexedScalarMeasureCuts
variable {L κ : ℝ} [Fact (0 < L)]

abbrev M (hκ : 0 < κ) (u : L2T L) := PhysicalQuantumMeasure.measure hκ u
abbrev theta (hκ : 0 < κ) (u : L2T L) (x : ℝ) :=
  (PhysicalContinuousBoundary.boundary hκ u x).re

def reG (hκ : 0 < κ) (u : L2T L) (x : ℝ) : ℝ := (L*x/2-theta hκ u x)/κ

theorem label_eq (hκ : 0 < κ) (u : L2T L) (x : ℝ) :
    indexLabel L κ (reG hκ u) x = theta hκ u x / Real.pi := by
  unfold indexLabel reG
  field_simp [hκ.ne', Real.pi_ne_zero]
  ring

theorem boundary_pointwise (hκ : 0 < κ) (u : L2T L) (x : ℝ) :
    Tendsto (fun ε => reCauchy (M hκ u) x ε) (𝓝[>] 0) (𝓝 (reG hκ u x)) := by
  have ht := (PhysicalSourceFinal.sourceFacts hκ u).boundary x
  have he : (fun ε : ℝ =>
      (L*x/2-(SpatialTransfer.boundaryPhase L κ (M hκ u)
        ((x : ℂ)+(ε : ℂ)*Complex.I)).re)/κ) =
      (fun ε => reCauchy (M hκ u) x ε) := by
    funext ε
    simp only [SpatialTransfer.boundaryPhase, Complex.sub_re, Complex.div_ofNat_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    unfold reCauchy
    field_simp [hκ.ne', Real.pi_ne_zero]
    ring
  exact he ▸ ((tendsto_const_nhds.sub (Complex.continuous_re.continuousAt.tendsto.comp ht)).div_const κ)

/-- The full upper boundary limits imply locally uniform bounds on the real Cauchy values. -/
theorem boundary_bounded (hκ : 0 < κ) (u : L2T L) :
    BoundedAEBoundary (M hκ u) (reG hκ u) := by
  refine ⟨?_, Eventually.of_forall (boundary_pointwise hκ u)⟩
  intro K hK
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (PhysicalContinuousBoundary.continuous_boundary hκ u).continuousOn
  obtain ⟨A, hA⟩ := hK.isBounded.exists_norm_le
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x ∈ K,
      ‖SpatialTransfer.boundaryPhase L κ (M hκ u) ((x : ℂ)+(ε : ℂ)*Complex.I)‖ < B+1 := by
    have hh : ∀ x ∈ K, ∀ᶠ p : ℝ × ℝ in (𝓝[>] 0) ×ˢ 𝓝 x,
        ‖SpatialTransfer.boundaryPhase L κ (M hκ u) ((p.2 : ℂ)+(p.1 : ℂ)*Complex.I)‖ < B+1 := by
      intro x hx
      have hz : Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ)+(p.1 : ℂ)*Complex.I)
          ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have hc : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)+(p.1 : ℂ)*Complex.I) := by fun_prop
          have ht := hc.tendsto (0,x)
          simp only [nhds_prod_eq, Complex.ofReal_zero, zero_mul, add_zero] at ht
          exact ht.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
        · have hp0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
          filter_upwards [hp0.prod_inl (𝓝 x)] with p hp
          change 0 < p.1 at hp
          simpa [PhysicalPhaseHolomorphic.upper] using hp
      have ht := (PhysicalContinuousBoundary.boundary_limit hκ u x).comp hz
      exact ht.norm.eventually (gt_mem_nhds ((hB x hx).trans_lt (lt_add_one B)))
    have hh' := hK.mem_prod_nhdsSet_of_forall hh
    have hh'' := Filter.Eventually.filter_mono
      (Filter.prod_mono le_rfl (principal_le_nhdsSet)) hh'
    simpa only [eventually_prod_principal_iff] using hh''
  obtain ⟨δ, hδ, hd⟩ := (nhdsGT_basis 0).mem_iff.mp hbound
  refine ⟨(|L| *A/2+(B+1))/κ, δ, hδ, ?_⟩
  intro ε hε x hx
  have hp := (hd hε) x hx
  have hre : L*x/2-κ*reCauchy (M hκ u) x ε =
      (SpatialTransfer.boundaryPhase L κ (M hκ u)
        ((x : ℂ)+(ε : ℂ)*Complex.I)).re := by
    simp [SpatialTransfer.boundaryPhase, reCauchy, Complex.mul_re]
  have hr : |L*x/2-κ*reCauchy (M hκ u) x ε| ≤ B+1 :=
    (hre ▸ (Complex.abs_re_le_norm _)).trans hp.le
  have hxa : |x| ≤ A := by simpa [Real.norm_eq_abs] using hA x hx
  have hl : |L*x/2| ≤ |L| *A/2 := by
    rw [abs_div, abs_mul]; norm_num; gcongr
  have hsum := norm_sub_le (L*x/2) (L*x/2-κ*reCauchy (M hκ u) x ε)
  have hs : |κ*reCauchy (M hκ u) x ε| ≤ |L| *A/2+(B+1) := by
    simp only [Real.norm_eq_abs, sub_sub_cancel] at hsum
    linarith
  rw [abs_mul, abs_of_pos hκ] at hs
  exact (le_div_iff₀ hκ).mpr (by nlinarith)

theorem integer_ae (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    ∀ᵐ x ∂(M hκ u), ∃ n : ℤ, indexLabel L κ (reG hκ u) x = n := by
  dsimp only [M]
  rw [RootDensityIdentification.root_density hκ hu]
  apply (ae_withDensity_iff (ENNReal.measurable_ofReal.comp (RootDensityIdentification.continuous_dens κ u).measurable)).mpr
  apply Eventually.of_forall
  intro x hx
  have hd : 0 < RootDensityIdentification.dens κ u x :=
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)
  have hg : 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| := by
    unfold RootDensityIdentification.dens at hd
    rw [mul_pos_iff_of_pos_left (by positivity : 0 < (Real.pi*κ)⁻¹)] at hd
    exact (RootDensity.hfun_pos_iff _).mp hd
  have hc : 2 * Complex.cos (PhysicalContinuousBoundary.boundary hκ u x) =
      ((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℂ) := by
    rw [PhysicalContinuousBoundary.boundary_cosine]
    exact Complex.ext (by simp) (by simp [L2DiscriminantRegularity.discriminant_real κ u x])
  obtain ⟨n, hn⟩ := PhysicalTraceSymbolDependency.gap_value_integer_pi hc hg
  refine ⟨n, ?_⟩
  rw [label_eq]
  change (PhysicalContinuousBoundary.boundary hκ u x).re / Real.pi = n
  rw [hn, mul_div_cancel_right₀ _ Real.pi_pos.ne']

def cuts (κ : ℝ) (u : L2T L) : Set ℝ :=
  {x | |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2}

theorem cuts_open (κ : ℝ) (u : L2T L) : IsOpen (cuts κ u) :=
  isOpen_lt (Complex.continuous_re.comp ((L2DiscriminantRegularity.continuous_discriminant κ u).comp
    Complex.continuous_ofReal)).abs continuous_const

theorem cuts_sub (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    cuts κ u ⊆ ((M hκ u).support)ᶜ := by
  intro x hx
  exact Measure.notMem_support_iff_exists.mpr ⟨cuts κ u, (cuts_open κ u).mem_nhds hx,
    PhysicalBandCauchy.measure_band_zero hκ hu (cuts_open κ u).measurableSet (fun _ ht => ht.le)⟩

theorem force_eq (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {x : ℝ} (hx : x ∈ cuts κ u) :
    exteriorForce L κ (M hκ u) x = 2*theta hκ u x := by
  rw [IndexedScalarMeasure.exteriorForce_eq_two_re_phase,
    ← PhysicalContinuousBoundary.band_eq hκ hu hx]

def scalarCuts (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) : IndexedScalarMeasureCuts L κ where
  hL := Fact.out
  hκ := hκ
  μ := M hκ u
  isProb := ⟨by rw [PhysicalQuantumMeasure.measure_univ, hu]; norm_num⟩
  noAtoms := PhysicalUnconditionalTrace.atomless hκ u
  reG := reG hκ u
  boundary := Or.inr (boundary_bounded hκ u)
  integer_ae := integer_ae hκ (by intro he; rw [he, norm_zero] at hu; norm_num at hu)
  cuts := cuts κ u
  cuts_sub := cuts_sub hκ (by intro he; rw [he, norm_zero] at hu; norm_num at hu)
  separation := by
    intro x hx a h1 h2
    have hne : u ≠ 0 := by intro he; rw [he, norm_zero] at hu; norm_num at hu
    rw [force_eq hκ hne hx] at h1 h2
    have hi := integer_ae hκ hne
    constructor
    · filter_upwards [hi] with t ht htx
      obtain ⟨n, hn⟩ := ht
      rw [hn]
      have hm := PhysicalContinuousBoundary.monotone_all hκ u htx.le
      have he := label_eq hκ u t
      rw [hn] at he
      have hpi := Real.pi_pos
      have ht' : theta hκ u t = n*Real.pi := ((eq_div_iff hpi.ne').mp he).symm
      have hnlt : (n : ℝ) < a+1 := by nlinarith
      exact_mod_cast (show n ≤ a by exact Int.lt_add_one_iff.mp (by exact_mod_cast hnlt))
    · filter_upwards [hi] with t ht hxt
      obtain ⟨n, hn⟩ := ht
      rw [hn]
      have hm := PhysicalContinuousBoundary.monotone_all hκ u hxt.le
      have he := label_eq hκ u t
      rw [hn] at he
      have hpi := Real.pi_pos
      have ht' : theta hκ u t = n*Real.pi := ((eq_div_iff hpi.ne').mp he).symm
      have hnlt : (a : ℝ) < n := by nlinarith
      exact_mod_cast (show a+1 ≤ n by exact Int.add_one_le_iff.mpr (by exact_mod_cast hnlt))

@[simp] theorem scalarCuts_measure (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    (scalarCuts hκ u hu).μ = PhysicalQuantumMeasure.measure hκ u := rfl

/-- Identification with any limiting probability law having the printed DEF-010 specification. -/
theorem physical_eq_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {μ : ProbabilityMeasure ℝ} (hμ : BulkResponseActual.IsLimitingRapidityMeasure L κ hκ u hu μ) :
    PhysicalQuantumMeasure.measure hκ u = (μ : Measure ℝ) := by
  have hne : u ≠ 0 := by intro he; rw [he, norm_zero] at hu; norm_num at hu
  rw [PhysicalL2Normalization.measure_eq_Mmeas, FullMass.Mmeas_of_ne κ hne, hu]
  norm_num
  have hd : FullMass.unitDir u = u := by simp [FullMass.unitDir, hu]
  apply congrArg (fun ν : ProbabilityMeasure ℝ => (ν : Measure ℝ))
  have hs : BulkResponseActual.IsLimitingRapidityMeasure L κ hκ u hu
      (FreeLimit.muKappa (FullMass.unitDir u) (FullMass.norm_unitDir hne) κ) := by
    simpa only [hd] using FreeLimit.muKappa_spec (FullMass.unitDir u) (FullMass.norm_unitDir hne) hκ
  exact hs.unique hμ


open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0 Gfull_eq)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.Prop019Deviation (deviation_of_bundle)
open QuantumNLS.Prop019Linearization (rect_mem rect_im_ne gammaN_abs)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT wlen)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.MPFixedContour (gam_background bgfamOfG_union)
open QuantumNLS.MPLinearizationContours (mp_linearization_contours)
open QuantumNLS.Prop009ProbeDev (exists_pos_le_all Gam_im_le)



open Classical
open Prop026Mixed (gEvent IsEventProj mixedGap)

/-- PROP-026 with the actual physical scalar datum constructed and hS discharged. -/
theorem prop026_mixed (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d k : ℕ) (R : Finset ℕ) (hRd : ∀ r ∈ R, r ≤ d) (T : ℕ → ℝ)
    -- the fixed-action datum
    {r : ℕ} {n : Fin r → ℤ} {xm xp hf : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ cuts κ u) (hxp : ∀ i, xp i ∈ cuts κ u) (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i)
    (hfh : ∀ i, hf i ≤ h)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ (M hκ u) (xm i))
    (h2 : ∀ i, exteriorForce L κ (M hκ u) (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ (M hκ u) (xp i))
    (h4 : ∀ i, exteriorForce L κ (M hκ u) (xp i) < 2 * Real.pi * (n i + 1))
    -- the fixed pieces (weights `θ_n`) lying on the fixed contours
    {nf : ℕ} (Pf : Fin nf → Piece) (Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : ∑ j, wlen (Pf j) ≤ Λ)
    (hPfZ : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i, (Pf j).γ τ ∈ Gam (xm i) (xp i) (hf i))
    (hPfreal : ∀ j, ∀ τ ∈ Ioo (0 : ℝ) 1, ((Pf j).γ τ).im ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ (EI : ∀ N : ℕ, Set (MArr N)) (ρI : ℕ → ℝ), (∀ N, 0 ≤ ρI N) ∧ Tendsto ρI atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (EI N)ᶜ) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N ∩ EI N)ᶜ) atTop (𝓝 0) ∧
      (∀ (N : ℕ) (hN : 0 < N), ∃ Pg PI P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
        IsEventProj hκ u hu hN (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N) Pg ∧ IsEventProj hκ u hu hN (EI N) PI ∧
        IsEventProj hκ u hu hN (gEvent L κ (μ : Measure ℝ) θ γ ρ h b N ∩ EI N) P ∧ P = Pg * PI ∧
        ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 ≤
          ‖(1 - Pg) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 + ‖(1 - PI) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧
        ∀ᶠ q : ℕ in atTop, ∀ (hN : 1 ≤ k + q) (φ : SymSector ℂ (L2T L) (k + q)), ‖φ‖ = 1 →
          (∀ m ∉ gEvent L κ (μ : Measure ℝ) θ γ ρ h b (k + q) ∩ EI (k + q),
            ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
          ∃ B : BgFam (NbhdN (cutN L θ (k + q)) h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) d₀ s₁ a₀ c₁,
            B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
            B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
            ∀ (t : ℕ → ℝ), (∀ r ∈ R, |t r| ≤ T r) →
              mixedGap L κ h k q (cutN L θ (k + q)) R t Pf B φ ≤
                ENNReal.ofReal (C * ((1 + cutN L θ (k + q)) ^ (d + 1) *
                  ((((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ)) +
                  ρI (k + q))) := by
  exact Prop026Mixed.prop026_mixed hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt
    d k R hRd T (scalarCuts hκ u hu) (physical_eq_limit hκ u hu hμ).symm
    hxm hxp hlt hfpos hfh h1 h2 h3 h4 Pf Λ hΛ0 hΛ hPfZ hPfreal

/-- The fixed-action projection with the same physical binding. -/
theorem fixed_projection (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {r : ℕ} {n : Fin r → ℤ} {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ cuts κ u) (hxp : ∀ i, xp i ∈ cuts κ u) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ (M hκ u) (xm i))
    (h2 : ∀ i, exteriorForce L κ (M hκ u) (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ (M hκ u) (xp i))
    (h4 : ∀ i, exteriorForce L κ (M hκ u) (xp i) < 2 * Real.pi * (n i + 1)) :
    ∃ (E : ∀ N : ℕ, Set (MArr N)) (ρ : ℕ → ℝ), (∀ N, 0 ≤ ρ N) ∧ Tendsto ρ atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) atTop (𝓝 0) ∧
      (∀ (N : ℕ) (hN : 0 < N), ∃ PE : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N,
        (∀ m, PE (meanField_physicalBasis L N hN hκ m) =
          (if m ∈ E N then (1 : ℂ) else 0) • meanField_physicalBasis L N hN hκ m) ∧
        PE * PE = PE ∧ ContinuousLinearMap.adjoint PE = PE ∧
        ‖(1 - PE) (QuantumNLS.HighMomentsOps.wvec N u)‖ ^ 2 =
          (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ) ∧
      ∀ᶠ N : ℕ in atTop, ∀ (hN : 1 ≤ N) (φ : physSector L N),
        (∀ m ∉ E N, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) →
        ∀ i, ∀ w ∈ Gam (xm i) (xp i) (h i),
          ‖(normalizedTransfer L κ N w - sf L κ (EmpiricalRapidity.cauchyTransform (M hκ u)) w •
            (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤ ρ N * ‖φ‖ := by
  exact Prop009FixedProjection.fixed_projection hκ u hu hμ (scalarCuts hκ u hu)
    (physical_eq_limit hκ u hu hμ).symm hxm hxp hlt hh h1 h2 h3 h4

end QuantumNLS.Prop026Bound

#print axioms QuantumNLS.Prop026Bound.scalarCuts
#print axioms QuantumNLS.Prop026Bound.physical_eq_limit
#print axioms QuantumNLS.Prop026Bound.prop026_mixed
#print axioms QuantumNLS.Prop026Bound.fixed_projection

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop026Bound." ||
        n.toString.startsWith "_private.QuantumNLS.Prop026Bound." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Prop026Bound audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
