import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.S05FreeEnergy38
import NlsGge.Birkhoff.S05FreeEnergy38c
import NlsGge.Birkhoff.F05Identity38k
import NlsGge.Birkhoff.F05Identity38j
import NlsGge.Birkhoff.F05Bridge38
import NlsGge.Birkhoff.F07MassMoment38c
import NlsGge.Birkhoff.F08Bare38h
import NlsGge.Birkhoff.H02Hierarchy38d
import NlsGge.Birkhoff.H03Diagonal38c
import NlsGge.Birkhoff.H03Monotone38
import NlsGge.Birkhoff.H03Diagonal38

/-! # Actual E01/E04 consumers, continuation A2

Additive specializations for S05, F05 (including L06.08b), F07, F08, H02, and H03 of
`paper/v2.tex` (SHA-256 `0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec`).
The same actual Birkhoff map and actual one-smoothing producer are used throughout.
All other generic binders and conclusions are retained. Companion results independent of
Birkhoff data are exported with their original arbitrary-data statements. L06.08a already
has the unconditional export `NlsGge.Birkhoff.L06_08a_free38`; it needs no specialization.
Compilation and axiom checks do not constitute independent source-fidelity approval.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory InformationTheory Filter Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Weights NlsGge.HierarchyRiccati.Core
open NlsGge.AblowitzLadik NlsGge.ThirdConsultation.PDE
open scoped ENNReal ContDiff BoundedContinuousFunction

namespace LiebLiniger.FixedPeriod.EXT

/-- S05. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. The actual Birkhoff Gibbs law is a probability measure and uniquely minimizes the extended
free energy at the finite value `-log Z_W`; the remainder expectation bound, exclusion of
infinite free energy from minimizers, and finite-free-energy entropy-chain identity all hold. -/
theorem actual_s05_variational (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    IsProbabilityMeasure (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ∧
    actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) = ENNReal.ofReal (-Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c)) ∧
    actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ≠ (⊤ : ℝ≥0∞) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      ENNReal.ofReal (-Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c)) ≤ actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ →
      (actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ = ENNReal.ofReal (-Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c)) ↔ ρ = actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c)) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ = (⊤ : ℝ≥0∞) →
      actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ ≠ ENNReal.ofReal (-Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c))) ∧
    ∫ z, actualBirkhoffInput38.toBirkhoffTop38.Rbar38 c z ∂(actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ≤ 1 / (Real.exp 1 * actualBirkhoffInput38.toBirkhoffTop38.ZW38 c) ∧
    (∀ ρ : Measure (ℤ → ℂ), IsProbabilityMeasure ρ → actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ ≠ (⊤ : ℝ≥0∞) →
      actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ =
        klDiv ρ (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) + ENNReal.ofReal (-Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c))) := by
  exact NlsGge.Birkhoff.BirkhoffTop38.S05_variational_38 actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- S05. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. The sequence-space measure `ρ` is arbitrary, its instance asserts that it is a probability
measure, and `h` asserts finite extended free energy. Then `ρ` is absolutely continuous with
respect to the product Gaussian, its log likelihood and actual remainder are integrable, its
relative entropy against the actual Gibbs law is finite, and the real entropy-chain identity
holds. -/
theorem actual_s05_free_energy_chain_real (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)
    (ρ : Measure (ℤ → ℂ)) [IsProbabilityMeasure ρ]
    (h : actualBirkhoffInput38.toBirkhoffTop38.freeEnergyW38 c ρ ≠ (⊤ : ℝ≥0∞)) :
    ρ ≪ fullWeightSequenceGaussian c ∧
    Integrable (llr ρ (fullWeightSequenceGaussian c)) ρ ∧
    Integrable (actualBirkhoffInput38.toBirkhoffTop38.Rbar38 c) ρ ∧
    klDiv ρ (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ≠ (⊤ : ℝ≥0∞) ∧
    (klDiv ρ (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c)).toReal =
      (klDiv ρ (fullWeightSequenceGaussian c)).toReal + ∫ z, actualBirkhoffInput38.toBirkhoffTop38.Rbar38 c z ∂ρ +
        Real.log (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c) := by
  exact NlsGge.Birkhoff.BirkhoffTop38.freeEnergyW38_chain_real actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper ρ h

/-- S05. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. The actual remainder is integrable against the actual Birkhoff Gibbs law, and its
expectation is at most `1 / (e Z_W)`. -/
theorem actual_s05_integral_remainder_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    Integrable (actualBirkhoffInput38.toBirkhoffTop38.Rbar38 c) (actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ∧
    ∫ z, actualBirkhoffInput38.toBirkhoffTop38.Rbar38 c z ∂(actualBirkhoffInput38.toBirkhoffTop38.muHatW38 c) ≤ 1 / (Real.exp 1 * actualBirkhoffInput38.toBirkhoffTop38.ZW38 c) := by
  exact NlsGge.Birkhoff.BirkhoffTop38.integral_Rbar_muHatW38_le actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- S05. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. For almost every field `u` under the actual physical Gibbs law, there exists a smooth
period-one representative `U`; for every such function `U`, smoothness proof `hU`, periodicity
proof `hper`, and equality identifying its L² class with `u`, all weighted local charges are
nonnegative, the extended spectral energy and full charge series are infinite, the real charge
series is not summable, and its finite partial sums tend to positive infinity. -/
theorem actual_s05_infinite_energy (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.toBirkhoffTop38.muW38 c),
      (∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u) ∧
      ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u →
        (∀ j : ℕ, 0 ≤ NlsGge.coefficient c j * localCharge38 U j) ∧
        spectralEnergyW38 c u = ⊤ ∧
        chargeSeriesW38 c U = ⊤ ∧
        ¬ Summable (fun j : ℕ => NlsGge.coefficient c j * localCharge38 U j) ∧
        Tendsto (fun J : ℕ => ∑ j ∈ Finset.range J, NlsGge.coefficient c j * localCharge38 U j)
          atTop atTop := by
  exact NlsGge.Birkhoff.BirkhoffTop38.S05_infiniteEnergy_38 actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- S05. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. Almost every field `u` under the actual physical Gibbs law lies in H¹ and has infinite
extended sum of nonnegative gap contributions. -/
theorem actual_s05_gap_sum_infinite (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.toBirkhoffTop38.muW38 c), SobolevSquareSummable 1 (physicalFourier u) ∧
      ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 c u n) = ⊤ := by
  exact NlsGge.Birkhoff.BirkhoffTop38.ae_muW38_gapSum_eq_top actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- F05. The implicit natural order `m` and real coefficient sequence `β` are arbitrary; `hm` proves
`m ≥ 2`, and `hβ` proves positivity of each coefficient through `m`. The Sobolev-weighted
reciprocal rates are summable; the Birkhoff Gaussian, its Sobolev realization, and the actual
finite-hierarchy Gibbs laws are probabilities; the Gaussian has the claimed almost-sure weighted
square summability; both actual partition functions lie in `(0,1]` for every finite mode set
`Λ`, and those along the standard exhaustion tend to `Z_m`. -/
theorem actual_f05_construction {m : ℕ} {β : ℕ → ℝ}
    (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) :
    Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / finiteHierarchyRate38 m β n) ∧
    IsProbabilityMeasure (gammaM38 m β) ∧
    (∀ᵐ z ∂(gammaM38 m β),
      Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) ∧
    IsProbabilityMeasure ((gammaM38 m β).map (gaussianRealization38 m)) ∧
    (0 < ZM38 actualBirkhoffInput38 m β ∧ ZM38 actualBirkhoffInput38 m β ≤ 1) ∧
    IsProbabilityMeasure (muHatM38 actualBirkhoffInput38 m β) ∧ IsProbabilityMeasure (muM38 actualBirkhoffInput38 m β) ∧
    (∀ Λ : Finset ℤ, 0 < ZΛM38 actualBirkhoffInput38 m β Λ ∧ ZΛM38 actualBirkhoffInput38 m β Λ ≤ 1) ∧
    Tendsto (fun N : ℕ => ZΛM38 actualBirkhoffInput38 m β (stdExh38 N)) atTop (𝓝 (ZM38 actualBirkhoffInput38 m β)) := by
  exact NlsGge.Birkhoff.F05_construction38 actualBirkhoffInput38 hm hβ

/-- F05. The implicit natural order `m` and real coefficient sequence `β` are arbitrary; `hm` proves
`m ≥ 2`, and `hβ` proves positivity of each coefficient through `m`. The actual finite-gap law
equals the normalized unmodified Fourier density, the exponential weight is integrable, its
integral equals the actual `Z_m ∈ (0,1]`, and the finite-gap relative normalizers tend to that
same integral. -/
theorem actual_f05_fourier_identity {m : ℕ} {β : ℕ → ℝ}
    (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) :
    muM38 actualBirkhoffInput38 m β = (gammaFM38 m β).withDensity
        (fun u => ENNReal.ofReal ((ZM38 actualBirkhoffInput38 m β)⁻¹ * Real.exp (-(Vm38 m β u)))) ∧
    Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u)) ∂(gammaFM38 m β) = ZM38 actualBirkhoffInput38 m β ∧
    (0 < ZM38 actualBirkhoffInput38 m β ∧ ZM38 actualBirkhoffInput38 m β ≤ 1) ∧
    Tendsto (fun N : ℕ => ZΛM38 actualBirkhoffInput38 m β (stdExh38 N)) atTop
      (𝓝 (∫ u, Real.exp (-(Vm38 m β u)) ∂(gammaFM38 m β))) := by
  exact NlsGge.Birkhoff.F05_cor_identity38 actualBirkhoffInput38 actualOneSmoothingInput38 hm hβ

/-- F05. The implicit real coefficients `β₀`, `β₁`, and `β₂` are arbitrary, and `h0`, `h1`, and `h2`
prove their positivity. The real Sobolev index `s` is arbitrary. The order-two Gaussian
realization is invariant under reflection, the potentials agree for every `u : Hm1 2`, the
actual finite-gap normalizer equals the direct Q4 normalizer, and the actual order-two Gibbs law
realized in H^s equals the direct Q4 law. -/
theorem actual_f05_l06_08b {β₀ β₁ β₂ : ℝ}
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
        (seqRealization38 (sobolevModeWeight s)) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (seqRealization38 (sobolevModeWeight s))) ∧
    (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
      alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
    ZM38 actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
    (muM38 actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
      alQ4Rho38 s β₀ β₁ β₂ := by
  exact NlsGge.Birkhoff.L06_08b_38 actualBirkhoffInput38 actualOneSmoothingInput38 h0 h1 h2 s

/-- F05. The implicit real coefficients `β₀`, `β₁`, and `β₂` are arbitrary, and `h0`, `h1`, and `h2`
prove their positivity. For any real Sobolev index `s`, the defined physical order-two Gaussian
realized in H^s equals the direct sequence-Gaussian realization. This companion is independent
of Birkhoff data. -/
theorem actual_f05_gaussian_two_realization {β₀ β₁ β₂ : ℝ}
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (gammaFM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (seqRealization38 (sobolevModeWeight s)) := by
  exact NlsGge.Birkhoff.gammaFM38_two_realization h0 h1 h2 s

/-- F05. The implicit real coefficients `β₀`, `β₁`, and `β₂` are arbitrary, and `h0`, `h1`, and `h2`
prove their positivity. The actual order-two finite-gap relative partition functions along the
standard exhaustion tend to the direct Q4 normalizer. -/
theorem actual_f05_finite_gap_two_normalizer {β₀ β₁ β₂ : ℝ}
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    Filter.Tendsto (fun N : ℕ => ZΛM38 actualBirkhoffInput38 2 (alQ4Beta38 β₀ β₁ β₂) (stdExh38 N)) Filter.atTop
      (nhds (alQ4Z2_38 β₀ β₁ β₂)) := by
  exact NlsGge.Birkhoff.tendsto_ZΛM38_two_alQ4 actualBirkhoffInput38 actualOneSmoothingInput38 h0 h1 h2

/-- F07. The natural hierarchy order `m`, its lower-bound proof `hm`, and the field `u ∈ H^(m-1)`
are arbitrary. The mass of `u` to power `m` is at most its continuous charge of order `2m-2`.
This companion has no Birkhoff or smoothing premise. -/
theorem actual_f07_moment_ineq (m : ℕ) (hm : 2 ≤ m) (u : Hm1 m) :
    (∑' n : ℤ, ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from u) n‖ ^ 2) ^ m ≤
      chargeSobolev38 m (m - 1) u := by
  exact NlsGge.Birkhoff.F07_momentineq38 m hm u

/-- F07. The implicit natural order `m` and real coefficient sequence `β` are arbitrary; `hm` proves
`m ≥ 2`, and `hβ` proves positivity of each coefficient through `m`. The implicit real tilt `δ`
is arbitrary; `hδ0` allows zero and `hδ` keeps it below the coefficient of the charge of order
`2m-2`. The charge-tilted exponential is integrable under the physical Gaussian and has integral
equal to the actual lowered-coefficient normalizer divided by `dDelta38`. -/
theorem actual_f07_tilted_integral {m : ℕ} {β : ℕ → ℝ} {δ : ℝ}
    (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
    (hδ0 : 0 ≤ δ) (hδ : δ < β (m - 1)) :
    Integrable (fun u : Hm1 m =>
      Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u)) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u) + δ * chargeSobolev38 m (m - 1) u) ∂(gammaFM38 m β) =
      ZM38 actualBirkhoffInput38 m (lowerCoef38 m β δ) / dDelta38 m β δ := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F07_tiltedIntegral38 actualBirkhoffInput38 actualOneSmoothingInput38 hm hβ hδ0 hδ

/-- F07. The implicit natural order `m` and real coefficient sequence `β` are arbitrary; `hm` proves
`m ≥ 2`, and `hβ` proves positivity of each coefficient through `m`. The implicit real tilt `δ`
is arbitrary; `hδ0` proves positivity and `hδ` bounds it by the coefficient of the charge of
order `2m-2`. The mass-tilted exponential is integrable under the physical Gaussian and its
integral is at most the actual lowered-coefficient normalizer divided by `dDelta38`. -/
theorem actual_f07_exp_mass {m : ℕ} {β : ℕ → ℝ} {δ : ℝ}
    (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
    (hδ0 : 0 < δ) (hδ : δ < β (m - 1)) :
    Integrable (fun u : Hm1 m =>
      Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m)) (gammaFM38 m β) ∧
    ∫ u, Real.exp (-(Vm38 m β u) + δ * (chargeSobolev38 m 0 u) ^ m) ∂(gammaFM38 m β) ≤
      ZM38 actualBirkhoffInput38 m (lowerCoef38 m β δ) / dDelta38 m β δ := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F07_expMass38 actualBirkhoffInput38 actualOneSmoothingInput38 hm hβ hδ0 hδ

/-- F08. The implicit natural order `m` and real coefficient sequence `β` are arbitrary; `hm` proves
`m ≥ 2`, and `hβ` proves positivity of each coefficient through `m`. Every Fourier cutoff `N`
has a positive bare normalizer and a probability law; the bare and limiting weights are
integrable and converge in L¹ on their common Gaussian space; the relative normalizers converge
to the actual finite-gap `Z_m`, and the bare field laws converge weakly to the actual finite-gap
law on H^(m-1). -/
theorem actual_f08_bare {m : ℕ} {β : ℕ → ℝ}
    (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j) :
    (∀ N : ℕ, 0 < ZcalBare38 m β N ∧ IsProbabilityMeasure (nuBare38 m β N)) ∧
    ((∀ N : ℕ, Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β (truncSobolev38 ((m - 1 : ℕ) : ℝ) N u))))
        (gammaFM38 m β)) ∧
      Integrable (fun u : Hm1 m => Real.exp (-(Vm38 m β u))) (gammaFM38 m β) ∧
      Tendsto (fun N : ℕ => ∫ u, |Real.exp (-(Vm38 m β (truncSobolev38 ((m - 1 : ℕ) : ℝ) N u))) -
          Real.exp (-(Vm38 m β u))| ∂(gammaFM38 m β)) atTop (𝓝 0)) ∧
    Tendsto (fun N : ℕ => ZcalBare38 m β N /
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N, (Real.pi / finiteHierarchyRate38 m β n)) atTop
      (𝓝 (ZM38 actualBirkhoffInput38 m β)) ∧
    Tendsto (fun N : ℕ => NlsGge.Birkhoff.BirkhoffInput38.nuBarePM38 hm hβ N) atTop (𝓝 (NlsGge.Birkhoff.BirkhoffInput38.muPM38 actualBirkhoffInput38 hm hβ)) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.F08_bare38 actualBirkhoffInput38 actualOneSmoothingInput38 hm hβ

/-- H02. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. The actual finite-hierarchy normalizers tend to the positive full normalizer; every order
`m ≥ 2` defines a probability supported in H^(m-1). For each natural `r`, support lies in H^r
once `m ≥ 2` and `r + 1 ≤ m`; for every bounded continuous real test `F` on that Sobolev
carrier, its integrals tend to those of the actual full Gibbs law. -/
theorem actual_h02_hierarchy_limit (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ((Tendsto (fun m : ℕ => actualBirkhoffInput38.toBirkhoffTop38.hierZ38 c m) atTop (𝓝 (actualBirkhoffInput38.toBirkhoffTop38.ZW38 c))) ∧ 0 < actualBirkhoffInput38.toBirkhoffTop38.ZW38 c) ∧
    (∀ m : ℕ, 2 ≤ m → 0 < actualBirkhoffInput38.toBirkhoffTop38.hierZ38 c m ∧ actualBirkhoffInput38.toBirkhoffTop38.hierZ38 c m ≤ 1 ∧
      IsProbabilityMeasure (actualBirkhoffInput38.toBirkhoffTop38.hierMu38 c m) ∧
      ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.toBirkhoffTop38.hierMu38 c m),
        SobolevSquareSummable ((m - 1 : ℕ) : ℝ) (physicalFourier u)) ∧
    ∀ r : ℕ,
      (∀ m : ℕ, 2 ≤ m → r + 1 ≤ m → ∀ᵐ u : PhysicalL2 ∂(actualBirkhoffInput38.toBirkhoffTop38.hierMu38 c m),
        SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
      ∀ F : SobolevCarrier38 (r : ℝ) →ᵇ ℝ,
        Tendsto (fun m : ℕ => ∫ u, F (physH38 r u) ∂(actualBirkhoffInput38.toBirkhoffTop38.hierMu38 c m)) atTop
          (𝓝 (∫ u, F (physH38 r u) ∂(actualBirkhoffInput38.toBirkhoffTop38.muW38 c))) := by
  exact NlsGge.Birkhoff.BirkhoffTop38.H02_hierarchy_limit_38 actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- H03. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. There is one deterministic threshold sequence `Nk` with `Nk k ≥ k` for every natural `k`,
chosen before every natural Sobolev order `r`; at each cutoff `N` the bare law of order
`diagOrder38 Nk N` is a probability with positive normalizer, and for every bounded continuous
real test `G` on H^r its integrals tend to the actual full Gibbs expectation. -/
theorem actual_h03_diagonal_explicit (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∃ Nk : ℕ → ℕ, (∀ k, k ≤ Nk k) ∧
      ∀ r : ℕ,
        (∀ N : ℕ, 0 < ZcalBare38 (diagOrder38 Nk N) (NlsGge.coefficient c) N ∧
          IsProbabilityMeasure
            (nuBareS38 (diagOrder38 Nk N) (NlsGge.coefficient c) N (r : ℝ))) ∧
        ∀ G : SobolevHilbert (r : ℝ) →ᵇ ℝ,
          Tendsto (fun N : ℕ =>
              ∫ u, G u ∂(nuBareS38 (diagOrder38 Nk N) (NlsGge.coefficient c) N (r : ℝ))) atTop
            (𝓝 (∫ u, G (physFS38 r u) ∂(actualBirkhoffInput38.muW38 c))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.H03_diagonal_explicit_38 actualBirkhoffInput38 actualOneSmoothingInput38 lower upper c hlower hbound hupper

/-- H03. `lower` and `upper` are real coefficient bounds, `c` is an arbitrary real sequence,
`hlower` proves the lower bound positive, and `hbound` and `hupper` bound every coefficient of
`c`. There is one deterministic natural-valued order function `m` tending to infinity and
bounded below by two at every natural cutoff `N`, chosen before every natural Sobolev order `r`.
Its bare laws have positive normalizers and are probabilities at each cutoff, and all bounded
continuous real tests `G` on H^r converge to their actual full Gibbs expectations. -/
theorem actual_h03_diagonal (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ (∀ N, 2 ≤ m N) ∧
      ∀ r : ℕ,
        (∀ N : ℕ, 0 < ZcalBare38 (m N) (NlsGge.coefficient c) N ∧
          IsProbabilityMeasure (nuBareS38 (m N) (NlsGge.coefficient c) N (r : ℝ))) ∧
        ∀ G : SobolevHilbert (r : ℝ) →ᵇ ℝ,
          Tendsto (fun N : ℕ => ∫ u, G u ∂(nuBareS38 (m N) (NlsGge.coefficient c) N (r : ℝ))) atTop
            (𝓝 (∫ u, G (physFS38 r u) ∂(actualBirkhoffInput38.muW38 c))) := by
  exact NlsGge.Birkhoff.BirkhoffInput38.H03_diagonal_38 actualBirkhoffInput38 actualOneSmoothingInput38 lower upper c hlower hbound hupper

/-- H03. For every natural-valued threshold sequence `Nk`, the explicit hierarchy choice
`diagOrder38 Nk` is monotone in the Fourier cutoff. No Birkhoff or threshold-bound premise is
needed. -/
theorem actual_h03_monotone_diag_order (Nk : ℕ → ℕ) :
    Monotone (diagOrder38 Nk) := by
  exact NlsGge.Birkhoff.monotone_diagOrder38 Nk

/-- H03. For every natural-valued threshold sequence `Nk` and natural Fourier cutoff `N`, the
explicit hierarchy order is at most `max 2 N`. No Birkhoff or threshold-bound premise is needed. -/
theorem actual_h03_diag_order_le (Nk : ℕ → ℕ) (N : ℕ) :
    diagOrder38 Nk N ≤ max 2 N := by
  exact NlsGge.Birkhoff.diagOrder38_le Nk N

/-- H03. The natural-valued threshold sequence `Nk` is arbitrary, and `hNk` proves `Nk k ≥ k` for
every natural `k`. The same explicit choice `diagOrder38 Nk` used in the diagonal convergence
wrapper tends to infinity. -/
theorem actual_h03_tendsto_diag_order (Nk : ℕ → ℕ) (hNk : ∀ k, k ≤ Nk k) :
    Tendsto (diagOrder38 Nk) atTop atTop := by
  exact NlsGge.Birkhoff.tendsto_diagOrder38 Nk hNk

end LiebLiniger.FixedPeriod.EXT

end
