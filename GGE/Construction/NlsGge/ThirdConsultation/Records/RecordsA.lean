import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.Birkhoff.S01Translation38
import NlsGge.Birkhoff.S03Measure38d
import NlsGge.Birkhoff.S05FreeEnergy38c
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Birkhoff.F05Bridge38
import NlsGge.Birkhoff.F07MassMoment38c
import NlsGge.Birkhoff.F08Bare38f
import NlsGge.Birkhoff.F08Bare38h
import NlsGge.Birkhoff.H02Hierarchy38d
import NlsGge.Birkhoff.H03Diagonal38c
import NlsGge.Birkhoff.H03Monotone38
import NlsGge.Atomic.F.F015
import NlsGge.Atomic.F.F024
import NlsGge.Atomic.F.F032
import NlsGge.Atomic.R.R069

                                                         
                                                                        
                                                                       
                                                                                 
                                                                                       
  

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Weights NlsGge.HierarchyRiccati.Core
open NlsGge.AblowitzLadik NlsGge.Analysis.RegularizedDeterminant
open scoped ENNReal BigOperators ContDiff InnerProductSpace BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.Records

local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
local notation "BT" => NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38
local notation "O" => NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38

/-- S01: actual translation equivariance and the physical/Fourier Hamiltonian conventions. -/
theorem S01_concrete :
    (∀ (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (θ : ℝ),
      (B).T (rotSeq38 θ x) = rotSeq38 θ ((B).T x)) ∧
    (∀ (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ),
      (B).T (rotSeq38 θ x) = rotSeq38 θ ((B).T x)) ∧
    (∀ (u : PhysicalL2) (θ : ℝ),
      (B).T (rotSeq38 θ (fourierSeq38 u)) = rotSeq38 θ ((B).Φ u)) ∧
    (∀ (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (θ : ℝ),
      (B).Tinv (rotSeq38 θ z) = rotSeq38 θ ((B).Tinv z)) ∧
    (∀ (t : ℝ) (u : PhysicalL2),
      fourierSeq38 (translateL2_38 t u) =
        rotSeq38 (-(2 * Real.pi * t)) (fourierSeq38 u)) ∧
    (∀ {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) (t : ℝ),
      HasDerivAt (fun s : ℝ => translateL2_38 s u) (translateL2_38 t w) t) ∧
    (∀ (x η : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
        (hη : η ∈ seqSobolev38 ((1 : ℕ) : ℝ)),
      HasDerivAt (fun s : ℝ => canHam38 (fun n => x n + (s : ℂ) * η n))
        (stdSymplectic38 (canField38 x) η) 0) ∧
    (∀ {u w : PhysicalL2} (hw : IsFourierDeriv38 u w) (v : PhysicalL2)
        (hv : SobolevSquareSummable 1 (physicalFourier v)),
      HasDerivAt (fun s : ℝ => -(momentumFourier38 (u + (s : ℂ) • v)) / 2)
        (omegaPhys38 w v) 0) := by
  exact ⟨(B).T_rotSeq38, (B).T_rotSeq38_h1, (B).T_rotSeq38_fourier,
    (B).Tinv_rotSeq38, fourierSeq38_translate38, @hasDerivAt_translate38,
    canonical_hamilton38, @hasDerivAt_neg_half_momentum_line38⟩

/-- S03: one measurable full-measure set works for every finite exhaustion. -/
theorem S03_concrete (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    (∃ Ω : Set (ℤ → ℂ), MeasurableSet Ω ∧ fullWeightSequenceGaussian c Ωᶜ = 0 ∧
      ∀ z ∈ Ω, Summable (fun n : ℤ => remainderSummand38 c ((BT).cleanΦinv z) n) ∧
        0 ≤ remainder38 c ((BT).cleanΦinv z) ∧
        ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
          (∀ N : ℕ, Summable (fun n : ℤ =>
            remainderSummand38 c ((BT).cleanΦinv (projFin38 (Λ N) z)) n)) ∧
          (∀ N : ℕ, 0 ≤ remainder38 c ((BT).cleanΦinv (projFin38 (Λ N) z))) ∧
          Tendsto (fun N : ℕ => remainder38 c ((BT).cleanΦinv (projFin38 (Λ N) z)))
            atTop (𝓝 (remainder38 c ((BT).cleanΦinv z)))) ∧
    (∀ m : ℕ,
      Summable (fun n : ℤ => sobolevWeight38 m n / fullWeightRate c n) ∧
      (∫⁻ z, sequenceEnergy (sobolevWeight38 m) z ∂fullWeightSequenceGaussian c) ≠ ⊤ ∧
      Integrable (fun z => (sequenceEnergy (sobolevWeight38 m) z).toReal)
        (fullWeightSequenceGaussian c) ∧
      (∫ z, (sequenceEnergy (sobolevWeight38 m) z).toReal ∂fullWeightSequenceGaussian c) =
        ∑' n : ℤ, sobolevWeight38 m n / fullWeightRate c n) ∧
    (Summable (fun n : ℤ => japaneseBracket n ^ (-(3 / 2) : ℝ)) ∧
      (∫⁻ z, sequenceEnergy (tailWeight38 c) z ∂fullWeightSequenceGaussian c) ≠ ⊤ ∧
      Integrable (fun z => (sequenceEnergy (tailWeight38 c) z).toReal)
        (fullWeightSequenceGaussian c) ∧
      (∫ z, (sequenceEnergy (tailWeight38 c) z).toReal ∂fullWeightSequenceGaussian c) =
        ∑' n : ℤ, japaneseBracket n ^ (-(3 / 2) : ℝ)) ∧
    (∀ᵐ z ∂fullWeightSequenceGaussian c, z ∈ Omega038 c) ∧
    (∀ (r : ℝ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 r)
        {Λ : ℕ → Finset ℤ} (hΛ : IsExhaustion38 Λ),
      Tendsto (fun N : ℕ => carrierMk38 r (projFin38 (Λ N) z)
        (finiteSupport_mem_seqSobolev38 r _ (finite_support_projFin38 (Λ N) z)))
        atTop (𝓝 (carrierMk38 r z hz))) ∧
    (0 < (BT).ZW38 c ∧ (BT).ZW38 c ≤ 1) ∧
    IsProbabilityMeasure ((BT).muW38 c) := by
  exact ⟨remainder_convergence_S03_38 BT lower upper c hlower hbound hupper,
    gaussian_sobolev_expectation38 lower upper c hlower hbound hupper,
    gaussian_tail_expectation38 lower upper c hlower hbound hupper,
    ae_mem_Omega038 lower upper c hlower hbound hupper,
    fun r z hz {_} hΛ => tendsto_carrier_proj38 r z hz hΛ,
    (BT).ZW38_pos_le_one lower upper c hlower hbound hupper,
    (BT).isProbabilityMeasure_muW38 lower upper c hlower hbound hupper⟩

/-- S05: extended free-energy minimization and unrenormalized infinite energy. -/
theorem S05_concrete (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    (IsProbabilityMeasure ((BT).muHatW38 c) ∧
      (BT).freeEnergyW38 c ((BT).muHatW38 c) = ENNReal.ofReal (-Real.log ((BT).ZW38 c)) ∧
      (BT).freeEnergyW38 c ((BT).muHatW38 c) ≠ (∞ : ℝ≥0∞) ∧
      (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
        ENNReal.ofReal (-Real.log ((BT).ZW38 c)) ≤ (BT).freeEnergyW38 c ρ) ∧
      (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
        ((BT).freeEnergyW38 c ρ = ENNReal.ofReal (-Real.log ((BT).ZW38 c)) ↔
          ρ = (BT).muHatW38 c)) ∧
      (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → (BT).freeEnergyW38 c ρ = (∞ : ℝ≥0∞) →
        (BT).freeEnergyW38 c ρ ≠ ENNReal.ofReal (-Real.log ((BT).ZW38 c))) ∧
      (∫ z, (BT).Rbar38 c z ∂(BT).muHatW38 c) ≤ 1 / (Real.exp 1 * (BT).ZW38 c) ∧
      (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → (BT).freeEnergyW38 c ρ ≠ (∞ : ℝ≥0∞) →
        (BT).freeEnergyW38 c ρ =
          klDiv ρ ((BT).muHatW38 c) + ENNReal.ofReal (-Real.log ((BT).ZW38 c)))) ∧
    (∀ᵐ u : PhysicalL2 ∂(BT).muW38 c,
      (∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u) ∧
      ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u →
        (∀ j : ℕ, 0 ≤ NlsGge.coefficient c j * localCharge38 U j) ∧
        spectralEnergyW38 c u = ⊤ ∧ chargeSeriesW38 c U = ⊤ ∧
        ¬ Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) ∧
        Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J,
          NlsGge.coefficient c j * localCharge38 U j) atTop atTop) ∧
    (∀ (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
        (h : (BT).freeEnergyW38 c ρ ≠ (∞ : ℝ≥0∞)),
      ρ ≪ fullWeightSequenceGaussian c ∧
      Integrable (llr ρ (fullWeightSequenceGaussian c)) ρ ∧
      Integrable ((BT).Rbar38 c) ρ ∧ klDiv ρ ((BT).muHatW38 c) ≠ (∞ : ℝ≥0∞) ∧
      (klDiv ρ ((BT).muHatW38 c)).toReal =
        (klDiv ρ (fullWeightSequenceGaussian c)).toReal +
          (∫ z, (BT).Rbar38 c z ∂ρ) + Real.log ((BT).ZW38 c)) := by
  exact ⟨(BT).S05_variational_38 lower upper c hlower hbound hupper,
    (BT).S05_infiniteEnergy_38 lower upper c hlower hbound hupper,
    fun ρ _ h => (BT).freeEnergyW38_chain_real lower upper c hlower hbound hupper ρ h⟩

/-- F01: real adjoints, unweighted Hilbert--Schmidt continuity, and finite determinants. -/
theorem F01_concrete :
    (∀ x : H0_38,
      ContinuousLinearMap.adjoint ((B).Lop x) * J38 _ * (B).Lop x = J38 _) ∧
    (∀ x : H0_38,
      ContinuousLinearMap.adjoint ((B).Bop x) = -(J38 _ * ((B).Linv x - 1) * J38 _)) ∧
    (∀ x1 ξ1 : H1_38,
      (B).Bop (i10_38 x1) (i10_38 ξ1) = i20_38 ((B).Dfwd O x1 ξ1)) ∧
    (∀ x1 : H1_38, IsHilbertSchmidt ((B).Bop (i10_38 x1))) ∧
    Continuous ((B).BHS O) ∧
    (∀ (x : H1_38) (N : ℕ),
      LinearMap.adjoint ((B).LNmap x N) * (cp38 N).JV * (B).LNmap x N =
        (cp38 N).JV - (cp38 N).resRange ((cp38 N).Qop ((B).LxN x N)) ((cp38 N).Qop_mem _)) ∧
    (∀ (x : H1_38) (N : ℕ), |(B).detLN x N| ^ 2 = (B).detMN x N) ∧
    (∀ x : H1_38, Tendsto (fun N : ℕ => |(B).detLN x N| ^ 2) atTop (𝓝 1)) ∧
    (∀ {K : Set H1_38}, IsCompact K →
      TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => |(B).detLN x N| ^ 2)
        (fun _ => (1 : ℝ)) atTop K) ∧
    (∀ (K : Set H1_38), IsCompact K →
      TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => |(B).detLN x N|)
        (fun _ : H1_38 => (1 : ℝ)) atTop K) := by
  exact ⟨(B).Lop_adjoint_mul, (B).Bop_adjoint, (B).Bop_incl O,
    (B).Bop_isHS O, (B).continuous_BHS O, (B).F01_04_operator,
    (B).F01_06_identity, (B).tendsto_sq_detLN O,
    fun {_} hK => (B).tendstoUniformlyOn_sq_detLN O hK,
    NlsGge.ThirdConsultation.R.r069_main⟩

/-- F05: exact Fourier identification, construction, Ramer density, and the m=2 bridge. -/
theorem F05_concrete :
    (∀ {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j),
    (Summable (fun n : ℤ =>
        sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / finiteHierarchyRate38 m β n) ∧
      IsProbabilityMeasure (gammaM38 m β) ∧
      (∀ᵐ z ∂gammaM38 m β,
        Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) ∧
      IsProbabilityMeasure ((gammaM38 m β).map (gaussianRealization38 m)) ∧
      (0 < ZM38 B m β ∧ ZM38 B m β ≤ 1) ∧
      IsProbabilityMeasure (muHatM38 B m β) ∧ IsProbabilityMeasure (muM38 B m β) ∧
      (∀ Λ : Finset ℤ, 0 < ZΛM38 B m β Λ ∧ ZΛM38 B m β Λ ≤ 1) ∧
      Tendsto (fun N : ℕ => ZΛM38 B m β (stdExh38 N)) atTop (𝓝 (ZM38 B m β))) ∧
    (muM38 B m β = (gammaFM38 m β).withDensity
        (fun u => ENNReal.ofReal ((ZM38 B m β)⁻¹ * Real.exp (-(Vm38 m β u)))) ∧
      Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
      (∫ u, Real.exp (-(Vm38 m β u)) ∂gammaFM38 m β) = ZM38 B m β ∧
      (0 < ZM38 B m β ∧ ZM38 B m β ≤ 1) ∧
      Tendsto (fun N : ℕ => ZΛM38 B m β (stdExh38 N)) atTop
        (𝓝 (∫ u, Real.exp (-(Vm38 m β u)) ∂gammaFM38 m β))) ∧
    ((S05 m β hm hβ).γE.map (T05 B hm hβ).symm =
      (S05 m β hm hβ).γE.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(D05 hm hβ x))))) ∧
    IsProbabilityMeasure (gammaFM38 m β) ∧
    (NlsGge.ThirdConsultation.F.finiteGapLaw m β = muM38 B m β ∧
      NlsGge.ThirdConsultation.F.finiteNormalizer m β = ZM38 B m β)) ∧
    (∀ {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ),
      ((((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
          (seqRealization38 (sobolevModeWeight s)) =
        (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map
          (seqRealization38 (sobolevModeWeight s))) ∧
      (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
        alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
      ZM38 B 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
      (muM38 B 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
        alQ4Rho38 s β₀ β₁ β₂) ∧
      ((gammaFM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
        (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map
          (seqRealization38 (sobolevModeWeight s))) ∧
      Tendsto (fun N : ℕ => ZΛM38 B 2 (alQ4Beta38 β₀ β₁ β₂) (stdExh38 N)) atTop
        (𝓝 (alQ4Z2_38 β₀ β₁ β₂))) := by
  constructor
  · intro m β hm hβ
    have h05 := F05_identity38 B O hm hβ
    have h15 := NlsGge.ThirdConsultation.F.f015 m hm β hβ
    have hZ : NlsGge.ThirdConsultation.F.finiteNormalizer m β = ZM38 B m β :=
      h15.2.2.1.symm.trans h05.2.2.1
    have hLaw : NlsGge.ThirdConsultation.F.finiteGapLaw m β = muM38 B m β := by
      rw [h15.1, h05.2.2.2]
      congr 1
      funext u
      rw [hZ, div_eq_inv_mul]
    exact ⟨F05_construction38 B hm hβ, F05_cor_identity38 B O hm hβ,
      ramer_density05 B O hm hβ, isProbabilityMeasure_gammaFM38 hm hβ, ⟨hLaw, hZ⟩⟩
  · intro β₀ β₁ β₂ h0 h1 h2 s
    exact ⟨L06_08b_38 B O h0 h1 h2 s,
      gammaFM38_two_realization h0 h1 h2 s,
      tendsto_ZΛM38_two_alQ4 B O h0 h1 h2⟩

/-- F07: mass coercivity, the exact Gaussian tilt, and both integrable exponential tilts. -/
theorem F07_concrete :
    (∀ (m : ℕ) (hm : 2 ≤ m) (u : Hm1 m),
      (∑' n : ℤ,
        ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n‖ ^ 2) ^ m ≤
          chargeSobolev38 m (m - 1) u) ∧
    (∀ {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j),
    (∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)),
      (0 < dDelta38 m β δ ∧
        HasProd (fun n : ℤ => finiteHierarchyRate38 m (lowerCoef38 m β δ) n /
          finiteHierarchyRate38 m β n) (dDelta38 m β δ)) ∧
      gammaFM38 m (lowerCoef38 m β δ) =
        (gammaFM38 m β).withDensity (tiltDensityH38 m δ (dDelta38 m β δ))) ∧
    (∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)),
      Integrable (fun u : Hm1 m =>
        Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u)) (gammaFM38 m β) ∧
      (∫ u, Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u)
        ∂gammaFM38 m β) = ZM38 B m (lowerCoef38 m β δ) / dDelta38 m β δ) ∧
    (∀ {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < β (m - 1)),
      Integrable (fun u : Hm1 m =>
        Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m)) (gammaFM38 m β) ∧
      (∫ u, Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m)
        ∂gammaFM38 m β) ≤ ZM38 B m (lowerCoef38 m β δ) / dDelta38 m β δ)) := by
  refine ⟨F07_momentineq38, ?_⟩
  intro m β hm hβ
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ0 hδ
    exact ⟨hasProd_dDelta38 hm hβ hδ0 hδ, gammaFM38_tilt hm hβ hδ0 hδ⟩
  · intro δ hδ0 hδ
    rcases eq_or_lt_of_le hδ0 with _ | hpos
    · exact (B).F07_tiltedIntegral38 O hm hβ hδ0 hδ
    · have h24 := NlsGge.ThirdConsultation.F.f024 m hm β hβ δ hpos hδ
      have hZ : NlsGge.ThirdConsultation.F.finiteNormalizer m (lowerCoef38 m β δ) =
          ZM38 B m (lowerCoef38 m β δ) :=
        (NlsGge.ThirdConsultation.F.f015 m hm (lowerCoef38 m β δ) h24.1).2.2.1.symm.trans
          (F05_identity38 B O hm h24.1).2.2.1
      refine ⟨h24.2.2.1, ?_⟩
      rw [h24.2.2.2.1, hZ, ← NlsGge.ThirdConsultation.F.f024_dDelta_eq m hm β δ]
  · intro δ hδ0 hδ
    exact (B).F07_expMass38 O hm hβ hδ0 hδ

/-- F08: unmodified finite-plane laws, common-space L1, normalizers, and weak convergence. -/
theorem F08_concrete :
    (∀ {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j),
    ((∀ N : ℕ, 0 < ZcalBare38 m β N ∧ IsProbabilityMeasure (nuBare38 m β N)) ∧
      ((∀ N : ℕ, Integrable (fun u : Hm1 m =>
          Real.exp (-(Vm38 m β (truncSobolev38 _ N u)))) (gammaFM38 m β)) ∧
        Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
        Tendsto (fun N : ℕ => ∫ u,
          |Real.exp (-(Vm38 m β (truncSobolev38 _ N u))) - Real.exp (-(Vm38 m β u))|
          ∂gammaFM38 m β) atTop (𝓝 0)) ∧
      Tendsto (fun N : ℕ => ZcalBare38 m β N /
        ∏ n ∈ Finset.Icc (-(N : ℤ)) N, (Real.pi / finiteHierarchyRate38 m β n)) atTop
        (𝓝 (ZM38 B m β)) ∧
      Tendsto (fun N : ℕ => NlsGge.Birkhoff.BirkhoffInput38.nuBarePM38 hm hβ N) atTop (𝓝 (NlsGge.Birkhoff.BirkhoffInput38.muPM38 B hm hβ))) ∧
    (∀ (N : ℕ) (z : FourierPlane N),
      EmPlane38 m β N z =
        spectralEnergy38 m β (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z)) ∧
    (0 < NlsGge.ThirdConsultation.F.finiteNormalizer m β ∧
      Tendsto (NlsGge.ThirdConsultation.F.finiteOrderRelativeZ m β) atTop
        (𝓝 (NlsGge.ThirdConsultation.F.finiteNormalizer m β)) ∧
      IsProbabilityMeasure (NlsGge.ThirdConsultation.F.finiteGapLaw m β) ∧
      (∀ N : ℕ, IsProbabilityMeasure (nuBare38 m β N)) ∧
      ∀ F : BoundedContinuousFunction (Hm1 m) ℝ,
        (∀ N : ℕ, (∫ u, F u ∂nuBare38 m β N) =
          (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
            NlsGge.ThirdConsultation.F.finiteOrderRelativeZ m β N) ∧
        Tendsto (fun N : ℕ =>
          (∫ u, F (truncSobolev38 _ N u) * weightFN38 m β N u ∂gammaFM38 m β) /
            NlsGge.ThirdConsultation.F.finiteOrderRelativeZ m β N) atTop
          (𝓝 (∫ u, F u ∂NlsGge.ThirdConsultation.F.finiteGapLaw m β)) ∧
        Tendsto (fun N : ℕ => ∫ u, F u ∂nuBare38 m β N) atTop
          (𝓝 (∫ u, F u ∂NlsGge.ThirdConsultation.F.finiteGapLaw m β)))) ∧
    (∀ {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂)
        {s : ℝ} (hs : s < 3 / 2),
      (∀ φ : SobolevHilbert s →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ u, φ u ∂nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s) atTop
          (𝓝 (∫ u, φ u ∂alQ4Rho38 s β₀ β₁ β₂))) ∧
      Tendsto (fun N : ℕ => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
        ∏ n ∈ Finset.Icc (-(N : ℤ)) N,
          (Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n)) atTop
        (𝓝 (alQ4Z2_38 β₀ β₁ β₂))) := by
  constructor
  · intro m β hm hβ
    exact ⟨(B).F08_bare38 O hm hβ, EmPlane_eq_spectral38 hm,
      NlsGge.ThirdConsultation.F.f032 m hm β hβ⟩
  · intro β₀ β₁ β₂ h0 h1 h2 s hs
    exact L06_08a_38 B O h0 h1 h2 hs

/-- H02: the finite hierarchy converges in every fixed integer Sobolev space. -/
theorem H02_concrete (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    (((Tendsto (fun m : ℕ => (BT).hierZ38 c m) atTop (𝓝 ((BT).ZW38 c))) ∧
        0 < (BT).ZW38 c) ∧
      (∀ m : ℕ, 2 ≤ m → 0 < (BT).hierZ38 c m ∧ (BT).hierZ38 c m ≤ 1 ∧
        IsProbabilityMeasure ((BT).hierMu38 c m) ∧
        ∀ᵐ u : PhysicalL2 ∂(BT).hierMu38 c m,
          SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u)) ∧
      ∀ r : ℕ,
        (∀ m : ℕ, 2 ≤ m → r + 1 ≤ m → ∀ᵐ u : PhysicalL2 ∂(BT).hierMu38 c m,
          SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
        ∀ F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ,
          Tendsto (fun m : ℕ => ∫ u, F (physH38 r u) ∂(BT).hierMu38 c m) atTop
            (𝓝 (∫ u, F (physH38 r u) ∂(BT).muW38 c))) ∧
    (∀ {g : ℤ → ℂ} {m : ℕ} (hm : 3 ≤ m) (n : ℤ) (hg : g ∈ Omega1_38 c),
      hierRate38 c m n * actualGapActionAllE02_38 ((BT).cleanΦinv (zHier38 c m g)) n =
        ‖g n‖ ^ 2) := by
  exact ⟨(BT).H02_hierarchy_limit_38 lower upper c hlower hbound hupper,
    fun {_} {_} hm n hg => (BT).hierRate_mul_action38 lower upper c hlower hbound hupper hm n hg⟩

/-- H03: one deterministic monotone order, shared by all integer Sobolev topologies. -/
theorem H03_concrete (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    (∃ (m Nk : ℕ → ℕ), m = diagOrder38 Nk ∧ (∀ k, k ≤ Nk k) ∧
      Tendsto m atTop atTop ∧ Monotone m ∧
      (∀ N : ℕ, 2 ≤ m N ∧ m N ≤ max 2 N) ∧
      ∀ r : ℕ,
        (∀ N : ℕ, 0 < ZcalBare38 (m N) (NlsGge.coefficient c) N ∧
          IsProbabilityMeasure (nuBareS38 (m N) (NlsGge.coefficient c) N (r : ℝ))) ∧
        ∀ G : SobolevHilbert (r : ℝ) →ᵇ ℝ,
          Tendsto (fun N : ℕ => ∫ u, G u ∂nuBareS38 (m N) (NlsGge.coefficient c) N (r : ℝ))
            atTop (𝓝 (∫ u, G (physFS38 r u) ∂(BT).muW38 c))) ∧
    (∀ {k : ℕ} (hk : 2 ≤ k) (r : ℕ) (hr : r ≤ k - 1)
        (G : SobolevHilbert (r : ℝ) →ᵇ ℝ),
      (∫ u, G (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u)
        ∂muM38 B k (NlsGge.coefficient c)) =
      ∫ u, G (physFS38 r u) ∂(BT).hierMu38 c k) := by
  constructor
  · obtain ⟨Nk, hNk, hlim⟩ :=
      (B).H03_diagonal_explicit_38 O lower upper c hlower hbound hupper
    exact ⟨diagOrder38 Nk, Nk, rfl, hNk, tendsto_diagOrder38 Nk hNk,
      monotone_diagOrder38 Nk,
      fun N => ⟨two_le_diagOrder38 Nk N, diagOrder38_le Nk N⟩, hlim⟩
  · intro k hk r hr G
    exact (B).integral_muM38_reSob_eq_hierMu38 lower c hlower hbound hk r hr G

end NlsGge.ThirdConsultation.Records
