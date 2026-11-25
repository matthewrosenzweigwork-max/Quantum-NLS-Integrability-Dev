import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.S01Equivariance38c
import NlsGge.Birkhoff.S03Measure38c
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05ChargeSeries38

/-!
# Actual E01/E04 consumers, author A

Source: `paper/v2.tex`, SHA-256
`0e7c2e61a06ab6886124c3891c73e0b8997ab71473eaf75b05c524098a58e3ec`.
Literal applications of existing generic theorems to the SAME actual Birkhoff
and one-smoothing producers; all other data remain arbitrary.

Coverage: S01 (forward/inverse rotation equivariance and physical coordinates),
S03 (one full-measure set for all exhaustions), F01 (Hilbert–Schmidt continuity,
symplectic compression, real determinants, compact uniformity and basis independence),
W04 (both weighted gains, identified analytic homeomorphism and inverse, and
Cameron–Martin membership), W05 (spectral and local-charge energy formulations).

S05, F05, F07, F08, H02 and H03 are absent: their required generic modules have
no objects in the assigned read-only CleanBuildX55-20261110 parent. No dependency
is built here. Compilation and axiom checks do not approve source fidelity;
that gate belongs to the independent reviewer.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.Weights NlsGge.HierarchyRiccati.Core
open NlsGge.Analysis.RegularizedDeterminant NlsGge.ThirdConsultation.PDE
open scoped ENNReal ContDiff

namespace LiebLiniger.FixedPeriod.EXT

/-- S01. For every complex integer sequence `x`, its square-summability proof `hx`, and real
angle `θ`, the actual forward Birkhoff/Fourier map commutes with the diagonal rotation. -/
theorem actual_s01_t_rot_seq (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (θ : ℝ) :
    actualBirkhoffInput38.T (rotSeq38 θ x) = rotSeq38 θ (actualBirkhoffInput38.T x) :=
  actualBirkhoffInput38.T_rotSeq38 x hx θ

/-- S01. For every complex integer sequence `x`, its `h¹` membership proof `hx`, and real
angle `θ`, the actual forward map commutes with the diagonal rotation. -/
theorem actual_s01_t_rot_seq_h1 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (θ : ℝ) :
    actualBirkhoffInput38.T (rotSeq38 θ x) = rotSeq38 θ (actualBirkhoffInput38.T x) :=
  actualBirkhoffInput38.T_rotSeq38_h1 x hx θ

/-- S01. For every period-one L² field `u` and real angle `θ`, applying the actual forward
map to its rotated reflected Fourier sequence equals rotating its actual Birkhoff sequence. -/
theorem actual_s01_t_rot_seq_fourier (u : PhysicalL2) (θ : ℝ) :
    actualBirkhoffInput38.T (rotSeq38 θ (fourierSeq38 u)) = rotSeq38 θ (actualBirkhoffInput38.Φ u) :=
  actualBirkhoffInput38.T_rotSeq38_fourier u θ

/-- S01. For every complex integer sequence `z`, its square-summability proof `hz`, and real
angle `θ`, the actual inverse map commutes with the diagonal rotation. -/
theorem actual_s01_tinv_rot_seq (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (θ : ℝ) :
    actualBirkhoffInput38.Tinv (rotSeq38 θ z) = rotSeq38 θ (actualBirkhoffInput38.Tinv z) :=
  actualBirkhoffInput38.Tinv_rotSeq38 z hz θ

/-- S03. `lower` and `upper` are real bounds, `c` any real coefficient sequence, `hlower`
proves the lower bound positive, and `hbound` and `hupper` bound every coefficient. One
measurable Gaussian-full set `Ω` works for every sample `z ∈ Ω` and every increasing
exhaustion `Λ` of the integers by finite sets. The actual inverse fields have summable
nonnegative remainders, both before and after every projection indexed by `N`, and the
projected remainders tend to the unprojected remainder along each such exhaustion. -/
theorem actual_s03_remainder_convergence (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∃ Ω : Set (ℤ → ℂ), MeasurableSet Ω ∧ fullWeightSequenceGaussian c Ωᶜ = 0 ∧
      ∀ z ∈ Ω, Summable (fun n : ℤ => remainderSummand38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv z) n) ∧
        0 ≤ remainder38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv z) ∧
        ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
          (∀ N : ℕ, Summable (fun n : ℤ =>
            remainderSummand38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv (projFin38 (Λ N) z)) n)) ∧
          (∀ N : ℕ, 0 ≤ remainder38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv (projFin38 (Λ N) z))) ∧
          Tendsto (fun N : ℕ => remainder38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv (projFin38 (Λ N) z))) atTop
            (𝓝 (remainder38 c (actualBirkhoffInput38.toBirkhoffTop38.cleanΦinv z))) :=
  NlsGge.Birkhoff.remainder_convergence_S03_38 actualBirkhoffInput38.toBirkhoffTop38 lower upper c hlower hbound hupper

/-- F01. For every base point `x` in the real `h⁰` carrier, the actual forward derivative
`L` satisfies `L* J L = J`, using the real Hilbert-space adjoint. -/
theorem actual_f01_lop_adjoint_mul (x : H0_38) :
    ContinuousLinearMap.adjoint (actualBirkhoffInput38.Lop x) * J38 ((0 : ℕ) : ℝ) * actualBirkhoffInput38.Lop x = J38 ((0 : ℕ) : ℝ) :=
  actualBirkhoffInput38.Lop_adjoint_mul x

/-- F01. For every base point `x` in the real `h⁰` carrier, the adjoint of the actual
derivative perturbation is `-J (Linv - Id) J`. -/
theorem actual_f01_bop_adjoint (x : H0_38) :
    ContinuousLinearMap.adjoint (actualBirkhoffInput38.Bop x) = -(J38 ((0 : ℕ) : ℝ) * (actualBirkhoffInput38.Linv x - 1) * J38 ((0 : ℕ) : ℝ)) :=
  actualBirkhoffInput38.Bop_adjoint x

/-- F01. For every `h¹` base point `x1`, the actual derivative perturbation at its `h⁰`
inclusion is Hilbert–Schmidt on the underlying real `h⁰` space. -/
theorem actual_f01_bop_is_hilbert_schmidt (x1 : H1_38) : IsHilbertSchmidt (actualBirkhoffInput38.Bop (i10_38 x1)) :=
  actualBirkhoffInput38.Bop_isHS actualOneSmoothingInput38 x1

/-- F01. For every `h¹` base point `x1`, the continuous linear map underlying its actual
Hilbert–Schmidt derivative perturbation equals the actual `Bop` at its `h⁰` inclusion. -/
theorem actual_f01_to_clm_bhs (x1 : H1_38) :
    HilbertSchmidt.toCLM (actualBirkhoffInput38.BHS actualOneSmoothingInput38 x1) = actualBirkhoffInput38.Bop (i10_38 x1) :=
  actualBirkhoffInput38.toCLM_BHS actualOneSmoothingInput38 x1

/-- F01. The actual derivative perturbation, bundled as a real Hilbert–Schmidt operator
on `h⁰`, is continuous in its arbitrary `h¹` base point. -/
theorem actual_f01_continuous_bhs : Continuous (actualBirkhoffInput38.BHS actualOneSmoothingInput38) :=
  actualBirkhoffInput38.continuous_BHS actualOneSmoothingInput38

/-- F01. For every `h¹` base point `x` and natural cutoff `N`, including zero, the real
adjoint symplectic product of the actual derivative compression equals the compressed
complex structure minus its discarded-block correction. -/
theorem actual_f01_compressed_operator (x : H1_38) (N : ℕ) :
    LinearMap.adjoint (actualBirkhoffInput38.LNmap x N) * (cp38 N).JV * actualBirkhoffInput38.LNmap x N =
      (cp38 N).JV - (cp38 N).resRange ((cp38 N).Qop (actualBirkhoffInput38.LxN x N)) ((cp38 N).Qop_mem (actualBirkhoffInput38.LxN x N)) :=
  actualBirkhoffInput38.F01_04_operator x N

/-- F01. For every `h¹` base point `x` and natural cutoff `N`, including zero, the squared
absolute real determinant of the actual derivative compression equals the real determinant
of the identity plus its discarded-block correction. -/
theorem actual_f01_determinant_identity (x : H1_38) (N : ℕ) : |actualBirkhoffInput38.detLN x N| ^ 2 = actualBirkhoffInput38.detMN x N :=
  actualBirkhoffInput38.F01_06_identity x N

/-- F01. For every `h¹` base point `x`, the Hilbert–Schmidt norm of the discarded block
of the actual derivative at projected base points tends to zero as the cutoff tends to infinity. -/
theorem actual_f01_discarded_block_tendsto (x : H1_38) :
    Tendsto (fun N : ℕ => ‖actualBirkhoffInput38.cHS actualOneSmoothingInput38 x N‖) atTop (𝓝 0) :=
  actualBirkhoffInput38.tendsto_norm_cHS actualOneSmoothingInput38 x

/-- F01. For every `h¹` base point `x`, the squared absolute ordinary real determinant
of the actual derivative compression tends to one as the natural cutoff tends to infinity. -/
theorem actual_f01_sq_det_tendsto (x : H1_38) :
    Tendsto (fun N : ℕ => |actualBirkhoffInput38.detLN x N| ^ 2) atTop (𝓝 1) :=
  actualBirkhoffInput38.tendsto_sq_detLN actualOneSmoothingInput38 x

/-- F01. `K` is any subset of the real `h¹` carrier and `hK` proves it compact. The squared
absolute ordinary real determinants of the actual derivative compressions converge uniformly
to one on `K` as the cutoff tends to infinity. -/
theorem actual_f01_sq_det_tendsto_uniformly_on {K : Set H1_38} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (N : ℕ) (x : H1_38) => |actualBirkhoffInput38.detLN x N| ^ 2) (fun (_x : H1_38) => (1 : ℝ)) atTop K :=
  actualBirkhoffInput38.tendstoUniformlyOn_sq_detLN actualOneSmoothingInput38 hK

/-- F01. `x` is any `h¹` base point, `N` any natural cutoff, `ι` any finite index type with
decidable equality, and `b` any real basis of the cutoff space indexed by `ι`. The actual
derivative determinant equals its matrix determinant in `b`, including weighted bases. -/
theorem actual_f01_det_eq_matrix_det (x : H1_38) (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (cp38 N).V) :
    actualBirkhoffInput38.detLN x N = Matrix.det (LinearMap.toMatrix b b (actualBirkhoffInput38.LNmap x N)) :=
  actualBirkhoffInput38.detLN_eq_matrix_det38 x N b

/-- F01. `x` is any `h¹` base point, `N` any natural cutoff, `ι` any finite index type with
decidable equality, and `b` any real basis of the cutoff space indexed by `ι`. The actual
correction determinant equals the determinant of the identity matrix plus its matrix in `b`. -/
theorem actual_f01_correction_det_eq_matrix_det (x : H1_38) (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (cp38 N).V) :
    actualBirkhoffInput38.detMN x N = Matrix.det (1 + LinearMap.toMatrix b b (actualBirkhoffInput38.MNmap x N)) :=
  actualBirkhoffInput38.detMN_eq_matrix_det38 x N b

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s` and every sequence
`x ∈ E_s`, the actual forward difference `T x - x` belongs to `E_(s-1)`. -/
theorem actual_w04_k_mem_e {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∀ x ∈ seqE38 c s, actualBirkhoffInput38.T x - x ∈ seqE38 c (s - 1) :=
  actualBirkhoffInput38.K_mem_E38 actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s`, the actual forward
difference is real analytic everywhere from `E_s` to `E_(s-1)`. -/
theorem actual_w04_analytic_k_e {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => actualBirkhoffInput38.T y - y) (actualBirkhoffInput38.K_mem_E38 actualOneSmoothingInput38 c s)) Set.univ :=
  actualBirkhoffInput38.analytic_K_E38 actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s` and every sequence
`x ∈ E_s`, the actual inverse difference `Tinv x - x` belongs to `E_(s-1)`. -/
theorem actual_w04_kinv_mem_e {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    ∀ x ∈ seqE38 c s, actualBirkhoffInput38.Tinv x - x ∈ seqE38 c (s - 1) :=
  actualBirkhoffInput38.Kinv_mem_E38 actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s`, the actual inverse
difference is real analytic everywhere from `E_s` to `E_(s-1)`. -/
theorem actual_w04_analytic_kinv_e {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (eMap38 c s (s - 1) (fun y => actualBirkhoffInput38.Tinv y - y) (actualBirkhoffInput38.Kinv_mem_E38 actualOneSmoothingInput38 c s))
      Set.univ :=
  actualBirkhoffInput38.analytic_Kinv_E38 actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s` and point `y`
of `E_s`, the actual weighted homeomorphism has exactly the actual forward coordinates. -/
theorem actual_w04_weighted_homeo_coordinates {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (y : ECarrier38 c s) :
    eCoe38 c s (actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s y) = actualBirkhoffInput38.T (eCoe38 c s y) :=
  actualBirkhoffInput38.weightedHomeoE38_apply actualOneSmoothingInput38 c s y

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s` and point `y`
of `E_s`, the inverse of the same actual weighted homeomorphism has the actual inverse coordinates. -/
theorem actual_w04_weighted_homeo_symm_coordinates {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) (y : ECarrier38 c s) :
    eCoe38 c s ((actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s).symm y) = actualBirkhoffInput38.Tinv (eCoe38 c s y) :=
  actualBirkhoffInput38.weightedHomeoE38_symm_apply actualOneSmoothingInput38 c s y

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s`, the actual
global homeomorphism of `E_s` is real analytic everywhere. -/
theorem actual_w04_analytic_weighted_homeo {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s) Set.univ :=
  actualBirkhoffInput38.analytic_weightedHomeoE38 actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. For any real order `s`, the inverse
of the same actual global homeomorphism of `E_s` is real analytic everywhere. -/
theorem actual_w04_analytic_weighted_homeo_symm {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ (actualBirkhoffInput38.weightedHomeoE38 actualOneSmoothingInput38 c s).symm Set.univ :=
  actualBirkhoffInput38.analytic_weightedHomeoE38_symm actualOneSmoothingInput38 c s

/-- W04. `lower` and `upper` are arbitrary real bounds, and `c` is any coefficient sequence
satisfying `BoundedCoefficients lower upper`. `s` is any real order and `hs` proves
`s ≤ 1`. For every sequence `x ∈ E_s`, both actual nonlinear differences belong to the
Cameron–Martin sequence space. The generic order range includes `1/2 < s < 3/4`. -/
theorem actual_w04_differences_mem_cm {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : s ≤ 1) :
    (∀ x ∈ seqE38 c s, actualBirkhoffInput38.T x - x ∈ weightedSubmodule (cmModeWeight c)) ∧
      (∀ x ∈ seqE38 c s, actualBirkhoffInput38.Tinv x - x ∈ weightedSubmodule (cmModeWeight c)) :=
  actualBirkhoffInput38.differences_mem_CM_38 actualOneSmoothingInput38 c hs

/-- W05 spectral energy. `lower` and `upper` are real bounds, `c` any coefficient sequence
satisfying those positive bounds, `s` any real order, and `hs` proves `s < 3/4`. Every field
`u` with reflected Fourier sequence in `E_s` has a summable continuous nonnegative remainder
for the topology transported from `E_s`. If its extended spectral energy is finite, its
actual action quadratic series is summable and its real energy is that series plus the remainder. -/
theorem actual_w05_spectral_energy {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : s < 3 / 4) :
    (∀ u : FinvE38 c s,
      Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) (inferInstance : TopologicalSpace ℝ) (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, spectralEnergyW38 c.val u.1 ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖actualBirkhoffInput38.Φ u.1 n‖ ^ 2) ∧
      (spectralEnergyW38 c.val u.1).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖actualBirkhoffInput38.Φ u.1 n‖ ^ 2 + remainder38 c.val u.1) :=
  actualBirkhoffInput38.W05_38 c s actualOneSmoothingInput38 hs

/-- W05 local-charge energy. `lower` and `upper` are real bounds, `c` any coefficient
sequence satisfying those positive bounds, `s` any real order, and `hs` proves `s < 3/4`.
Every field `u` with reflected Fourier sequence in `E_s` has a summable continuous nonnegative
remainder and a smooth period-one representative. For every representative `U : ℝ → ℂ`,
smoothness proof `hU`, periodicity proof `hper`, and equality of its L² class with `u`, finite
extended charge energy implies summability of the actual action quadratic series and the
real energy identity. Spectral and local-charge extended energies agree for every such
representative, including infinite energies. -/
theorem actual_w05_charge_series {lower upper : ℝ} {c : BoundedCoefficients lower upper} {s : ℝ} (hs : s < 3 / 4) :
    (∀ u : FinvE38 c s, Summable (fun n : ℤ => remainderSummand38 c.val u.1 n)) ∧
    @Continuous (FinvE38 c s) ℝ (topFinvE38 c s) (inferInstance : TopologicalSpace ℝ) (fun u => remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, 0 ≤ remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → chargeSeriesW38 c.val U ≠ ⊤ →
      Summable (fun n : ℤ => fullWeightRate c.val n * ‖actualBirkhoffInput38.Φ u.1 n‖ ^ 2) ∧
      (chargeSeriesW38 c.val U).toReal =
        ∑' n : ℤ, fullWeightRate c.val n * ‖actualBirkhoffInput38.Φ u.1 n‖ ^ 2 + remainder38 c.val u.1) ∧
    (∀ u : FinvE38 c s, ∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 → spectralEnergyW38 c.val u.1 = chargeSeriesW38 c.val U) :=
  actualBirkhoffInput38.W05_chargeSeries_38 actualOneSmoothingInput38 hs

end LiebLiniger.FixedPeriod.EXT
