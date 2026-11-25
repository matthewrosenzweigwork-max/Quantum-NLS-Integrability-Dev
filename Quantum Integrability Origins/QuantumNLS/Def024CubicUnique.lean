import QuantumNLS.Def024CubicClassical
import QuantumNLS.LocalWellPosednessFull
import QuantumNLS.ChargeEnergy
import QuantumNLS.Def024LowEquivariance

/-!
# DEF-024, stage D1: uniqueness of the order-2 Hamiltonian flow (cubic NLS)

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex`), the frozen
`HierarchyFlow.IsHamFlow` for `F = Re I_3 = hamiltonian L κ 2`, and the classical reduction
`Def024CubicClassical.isHamFlow_two_iff` (frozen `a64696e9`).

Route (read-only inputs): `LocalWellPosednessFull.IsDistSol` and `dist_unique` (frozen, `κ ≥ 0`),
`ChargeEnergy.smooth_h04`, `WeakDerivatives.integral_chi_mul_deriv`, `Fourier.ae_eq_seriesRep`,
`Fourier.hasSum_sq_coeff`, `ChargeEnergy.hasSum_kinetic`, `LocalWellPosedness.Fh`.

What this module proves (for `κ ≥ 0`):
* `smH1`: a smooth periodic profile as an element of `h^1`, with coefficients `(√L)⁻¹ ∫₀^L χ_n u`;
* `Fh_val_smH1` (the plumbing lemma): `(Fh (smH1 u)).val n = (√L)⁻¹ ∫₀^L χ_n |u|² u`;
* `hasDerivAt_cIntg`: for a Hamiltonian flow `Φ`, the coefficient `s ↦ ∫₀^L χ_n Φ_s u₀` is
  differentiable with `∂_s = −i (n² c + 2κ N)` (the Fourier form of `∂_sΦ = −i cubicGrad Φ`);
* `weak_of_ode`: integration by parts against test functions gives the weak form;
* `continuous_smH1`: `t ↦ smH1 (Φ_t u₀)` is continuous into `h^1` (Parseval + uniform continuity);
* `isDistSol_of_flow`: `IsDistSol κ univ`;
* `unique_two`: `UniqueHamFlow L (hamiltonian L κ 2) Φ` for every `IsHamFlow` `Φ` (κ ≥ 0).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory Filter Topology Set

namespace QuantumNLS.Def024CubicUnique

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024Gradient
  QuantumNLS.Def024CubicGradient QuantumNLS.Def024CubicClassical
  QuantumNLS.WeakDerivatives QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
  QuantumNLS.Def024LowEquivariance
  QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.ChargeEnergy

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Interval coefficients and the `h^1` element of a smooth profile -/

/-- `∫₀^L χ_n(x) u(x) dx`, the interval form of the Fourier coefficient. -/
def cIntg (L : ℝ) (u : ℝ → ℂ) (n : ℤ) : ℂ := ∫ x in (0 : ℝ)..L, chi L n x * u x

/-- The cubic nonlinearity `|u|² u`. -/
def nlCub (u : ℝ → ℂ) : ℝ → ℂ := fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) * u x

/-- A smooth periodic profile as an element of `h^1` (through `smooth_h04`). -/
def smH1 {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : h04 L 1 :=
  h04.ofMem (smooth_h04 hu).2

theorem smH1_val {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    (smH1 hu).val n = coeff L (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) n :=
  rfl

theorem chi_continuous (n : ℤ) : Continuous (chi L n) :=
  (chi_isTest (L := L) n).smooth.continuous

theorem coeff_eq_cIntg {G : AddCircle L → ℂ} {g : ℝ → ℂ}
    (hG : ∀ x : ℝ, G (x : AddCircle L) = g x) (n : ℤ) :
    coeff L G n = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L g n := by
  rw [coeff_eq_interval]
  simp only [cIntg, hG]

theorem coeff_liftC_eq {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    coeff L (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) n =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L u n :=
  coeff_eq_cIntg (fun x => liftC_coe hu.smooth.continuous hu.periodic x) n

theorem smH1_val' {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    (smH1 hu).val n = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L u n :=
  (smH1_val hu n).trans (coeff_liftC_eq hu n)

/-- **Plumbing lemma.** The `n`-th coefficient of `F(f) = |f|² f` on the `h^1` element of a smooth
profile is the `n`-th coefficient of `|u|² u`. -/
theorem Fh_val_smH1 {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    (Fh (le_refl (1 : ℝ)) (smH1 hu)).val n = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (nlCub u) n := by
  set F : AddCircle L → ℂ := (liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) with hF
  have hmem : MemLp F 2 (volume : Measure (AddCircle L)) := (smooth_h04 hu).1
  have hae := ae_eq_seriesRep hmem (smooth_h04 hu).2
  have hG : nlRep L (coeff L F) =ᵐ[volume] fun x => ((‖F x‖ ^ 2 : ℝ) : ℂ) * F x := by
    filter_upwards [hae] with x hx
    unfold nlRep
    rw [← hx]
  have h1 : (Fh (le_refl (1 : ℝ)) (smH1 hu)).val n = coeff L (nlRep L (coeff L F)) n := rfl
  rw [h1, coeff_congr_ae L hG n, coeff_eq_cIntg (g := nlCub u) ?_ n]
  intro x
  simp [hF, nlCub, liftC_coe]

/-! ## 2. Joint smoothness of spatial derivatives -/

theorem contDiff_slice_deriv {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => G (p.1, y)) p.2) := by
  have key : ∀ p : ℝ × ℝ, deriv (fun y => G (p.1, y)) p.2 = fderiv ℝ G p (0, 1) := by
    intro p
    have hG' : HasFDerivAt G (fderiv ℝ G p) p :=
      ((hG.differentiable (by simp)) p).hasFDerivAt
    have hline : HasDerivAt (fun y : ℝ => (p.1, y)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
    have h2 : deriv (fun y => G (p.1, y)) p.2 = fderiv ℝ G (p.1, p.2) (0, 1) :=
      (hG'.comp_hasDerivAt p.2 hline).deriv
    exact h2
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => fderiv ℝ G p (0, 1)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  simp only [key]
  exact hc

theorem contDiff_slice_deriv2 {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun y => deriv (fun z => G (p.1, z)) y) p.2) :=
  contDiff_slice_deriv (contDiff_slice_deriv hG)

theorem nlCub_continuous {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : Continuous (nlCub u) := by
  unfold nlCub
  have := hu.smooth.continuous
  fun_prop

/-! ## 3. The cubic functional on Fourier coefficients -/

/-- The integral of the Hamiltonian gradient against `χ_n`: `∫ χ_n · cubicGrad u = n² û + 2κ N̂`. -/
theorem integral_chi_cubicGrad {κ : ℝ} {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) :
    ∫ x in (0 : ℝ)..L, chi L n x * cubicGrad κ u x =
      ((freq L n ^ 2 : ℝ) : ℂ) * cIntg L u n + ((2 * κ : ℝ) : ℂ) * cIntg L (nlCub u) n := by
  have hu1 : SmoothPeriodic L (deriv u) := cub_smoothPeriodic_deriv hu
  have hc := chi_continuous (L := L) n
  have hdd : Continuous (deriv (deriv u)) := deriv_continuous hu1
  have hnl := nlCub_continuous hu
  have hsplit : (fun x => chi L n x * cubicGrad κ u x) =
      fun x => -(chi L n x * deriv (deriv u) x) + ((2 * κ : ℝ) : ℂ) * (chi L n x * nlCub u x) := by
    funext x
    simp only [cubicGrad, nlCub]
    push_cast
    ring
  have hA : IntervalIntegrable (fun x => chi L n x * deriv (deriv u) x) volume 0 L :=
    (hc.mul hdd).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x => chi L n x * nlCub u x) volume 0 L :=
    (hc.mul hnl).intervalIntegrable _ _
  have h1 : ∫ x in (0 : ℝ)..L, chi L n x * deriv u x =
      ikn L n * ∫ x in (0 : ℝ)..L, chi L n x * u x :=
    integral_chi_mul_deriv hu n
  have h2 : ∫ x in (0 : ℝ)..L, chi L n x * deriv (deriv u) x =
      ikn L n * ∫ x in (0 : ℝ)..L, chi L n x * deriv u x :=
    integral_chi_mul_deriv hu1 n
  unfold cIntg
  have hA' : IntervalIntegrable (fun x => -(chi L n x * deriv (deriv u) x)) volume 0 L :=
    hA.neg
  have hB' : IntervalIntegrable (fun x => ((2 * κ : ℝ) : ℂ) * (chi L n x * nlCub u x)) volume 0 L :=
    hB.const_mul _
  rw [hsplit, intervalIntegral.integral_add hA' hB', intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, h2, h1]
  unfold ikn
  push_cast
  linear_combination (-(freq L n : ℂ) ^ 2 *
    ∫ x in (0 : ℝ)..L, chi L n x * u x) * Complex.I_sq

/-! ## 4. The time derivative of a coefficient along a Hamiltonian flow -/

/-- **Coefficient ODE.** For `Φ` a Hamiltonian flow of `Re I_3` (in the classical form of
`isHamFlow_two_iff`), `s ↦ ∫₀^L χ_n Φ_s u₀` has derivative `−i (n² c + 2κ N)`. -/
theorem hasDerivAt_cIntg {κ : ℝ} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} {u0 : ℝ → ℂ}
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u0 p.2))
    (hper : ∀ s, SmoothPeriodic L (Φ s u0))
    (hpde : ∀ s x, HasDerivAt (fun s' => Φ s' u0 x) (-Complex.I * cubicGrad κ (Φ s u0) x) s)
    (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s => cIntg L (Φ s u0) n)
      (-Complex.I * (((freq L n ^ 2 : ℝ) : ℂ) * cIntg L (Φ t u0) n +
        ((2 * κ : ℝ) : ℂ) * cIntg L (nlCub (Φ t u0)) n)) t := by
  have hGc : Continuous (fun p : ℝ × ℝ => Φ p.1 u0 p.2) := hsm.continuous
  have hKc : Continuous (fun p : ℝ × ℝ => -Complex.I * cubicGrad κ (Φ p.1 u0) p.2) := by
    have hE : Continuous (fun p : ℝ × ℝ => deriv (deriv (Φ p.1 u0)) p.2) :=
      (contDiff_slice_deriv2 hsm).continuous
    have hN : Continuous (fun p : ℝ × ℝ => ((‖Φ p.1 u0 p.2‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_norm.comp hGc).pow 2)
    unfold cubicGrad
    exact continuous_const.mul (hE.neg.add ((continuous_const.mul hN).mul hGc))
  have hKt : Continuous (fun y => -Complex.I * cubicGrad κ (Φ t u0) y) :=
    hKc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ Metric.closedBall t 1 ×ˢ uIcc (0 : ℝ) L,
      ‖chi L n p.2 * (-Complex.I * cubicGrad κ (Φ p.1 u0) p.2)‖ ≤ M :=
    ((isCompact_closedBall t 1).prod isCompact_uIcc).exists_bound_of_continuousOn
      ((((chi_continuous n).comp continuous_snd).mul hKc).continuousOn)
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := L)
    (F := fun s x => chi L n x * Φ s u0 x)
    (F' := fun s x => chi L n x * (-Complex.I * cubicGrad κ (Φ s u0) x))
    (x₀ := t) (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s =>
      (((chi_continuous n).mul (hper s).smooth.continuous)).aestronglyMeasurable)
    (((chi_continuous n).mul (hper t).smooth.continuous).intervalIntegrable _ _)
    (((chi_continuous n).mul hKt).aestronglyMeasurable)
    (ae_of_all _ fun y hy s' hs' => hM (s', y)
      ⟨Metric.ball_subset_closedBall hs', uIoc_subset_uIcc hy⟩)
    intervalIntegrable_const
    (ae_of_all _ fun y _ s' _ => (hpde s' y).const_mul (chi L n y))
  have h3 : HasDerivAt (fun s => cIntg L (Φ s u0) n)
      (∫ x in (0 : ℝ)..L, chi L n x * (-Complex.I * cubicGrad κ (Φ t u0) x)) t := hint.2
  have hval : ∫ x in (0 : ℝ)..L, chi L n x * (-Complex.I * cubicGrad κ (Φ t u0) x) =
      -Complex.I * (((freq L n ^ 2 : ℝ) : ℂ) * cIntg L (Φ t u0) n +
        ((2 * κ : ℝ) : ℂ) * cIntg L (nlCub (Φ t u0)) n) := by
    have e : ∫ x in (0 : ℝ)..L, chi L n x * (-Complex.I * cubicGrad κ (Φ t u0) x) =
        -Complex.I * ∫ x in (0 : ℝ)..L, chi L n x * cubicGrad κ (Φ t u0) x := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      ring
    rw [e, integral_chi_cubicGrad (hper t) n]
  rw [hval] at h3
  exact h3

/-! ## 5. Integration by parts against test functions -/

/-- **Weak form of a linear ODE.** If `A' = −i(λ A + μ B)` with `A, B` continuous, then tested
against a `C_c^∞` function, `−i ∫ φ' A = ∫ φ (λ A + μ B)`. -/
theorem weak_of_ode {A B : ℝ → ℂ} {lam mu : ℂ}
    (hA : ∀ t, HasDerivAt A (-Complex.I * (lam * A t + mu * B t)) t)
    (hAc : Continuous A) (hBc : Continuous B) {φ : ℝ → ℝ} (hφ : IsTest univ φ) :
    -Complex.I * ∫ t, deriv φ t • A t = ∫ t, φ t • (lam * A t + mu * B t) := by
  have hφd : ∀ t, HasDerivAt (fun t => (φ t : ℂ)) ((deriv φ t : ℝ) : ℂ) t := fun t =>
    ((hφ.1.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hφc : Continuous fun t => (φ t : ℂ) := Complex.continuous_ofReal.comp hφ.1.continuous
  have hdφ := hφ.deriv
  have hφ'c : Continuous fun t => ((deriv φ t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hdφ.1.continuous
  have hφs : HasCompactSupport fun t => (φ t : ℂ) :=
    hφ.2.1.comp_left Complex.ofReal_zero
  have hφ's : HasCompactSupport fun t => ((deriv φ t : ℝ) : ℂ) :=
    hdφ.2.1.comp_left Complex.ofReal_zero
  have hX : Continuous fun t => -Complex.I * (lam * A t + mu * B t) :=
    continuous_const.mul ((continuous_const.mul hAc).add (continuous_const.mul hBc))
  have hint1 : Integrable fun t => (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t)) :=
    (hφc.mul hX).integrable_of_hasCompactSupport (hφs.mul_right)
  have hint2 : Integrable fun t => ((deriv φ t : ℝ) : ℂ) * A t :=
    (hφ'c.mul hAc).integrable_of_hasCompactSupport (hφ's.mul_right)
  have hint3 : Integrable fun t => (φ t : ℂ) * A t :=
    (hφc.mul hAc).integrable_of_hasCompactSupport (hφs.mul_right)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => (φ t : ℂ)) (u' := fun t => ((deriv φ t : ℝ) : ℂ)) (v := A)
    (v' := fun t => -Complex.I * (lam * A t + mu * B t))
    (fun t _ => hφd t) (fun t _ => hA t) hint1 hint2 hint3
  beta_reduce at ibp
  have key : ∫ t, ((deriv φ t : ℝ) : ℂ) * A t =
      -(∫ t, (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t))) := by
    rw [ibp, neg_neg]
  have e1 : ∫ t, (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t)) =
      -Complex.I * ∫ t, (φ t : ℂ) * (lam * A t + mu * B t) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  simp only [Complex.real_smul]
  rw [key, e1]
  linear_combination (-(∫ t, (φ t : ℂ) * (lam * A t + mu * B t))) * Complex.I_sq

/-! ## 6. Continuity of the coefficient map into `h^1` -/

theorem smooth_sub {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) :
    SmoothPeriodic L (fun x => f x - g x) :=
  ⟨hf.smooth.sub hg.smooth, fun x => by simp only [hf.periodic x, hg.periodic x]⟩

theorem cIntg_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cIntg L (fun x => f x - g x) n = cIntg L f n - cIntg L g n := by
  unfold cIntg
  have hA : IntervalIntegrable (fun x => chi L n x * f x) volume 0 L :=
    ((chi_continuous n).mul hf).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x => chi L n x * g x) volume 0 L :=
    ((chi_continuous n).mul hg).intervalIntegrable _ _
  simp only [mul_sub]
  exact intervalIntegral.integral_sub hA hB

theorem integral_addCircle_sq {g : ℝ → ℂ} (hg : SmoothPeriodic L g) :
    ∫ t : AddCircle L, ‖(liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) t‖ ^ 2
        ∂(volume : Measure (AddCircle L)) =
      ∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2 := by
  have h := AddCircle.intervalIntegral_preimage L 0
    (fun t : AddCircle L => ‖(liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) t‖ ^ 2)
  simp only [zero_add] at h
  rw [← h]
  simp [liftC_coe]

/-- **Continuity into `h^1`.** For a joint-smooth Hamiltonian family, `t ↦ smH1 (Φ_t u₀)` is
continuous. Proof: `‖Δ‖²_{h^1} = ∫₀^L |g|² + ∫₀^L |g'|²` (Parseval, `hasSum_sq_coeff`,
`hasSum_kinetic`) for `g = Φ_t u₀ − Φ_{t₀} u₀`, and both integrands are uniformly small on `[0,L]`
for `t` near `t₀` by uniform continuity on a compact box. -/
theorem continuous_smH1 {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} {u0 : ℝ → ℂ}
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u0 p.2))
    (hper : ∀ s, SmoothPeriodic L (Φ s u0)) :
    Continuous (fun t => smH1 (hper t) : ℝ → h04 L 1) := by
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  rw [Metric.continuousAt_iff]
  intro η hη
  have hLpos : 0 < L := Fact.out
  have hGc : Continuous (fun p : ℝ × ℝ => Φ p.1 u0 p.2) := hsm.continuous
  have hDc : Continuous (fun p : ℝ × ℝ => deriv (Φ p.1 u0) p.2) :=
    (contDiff_slice_deriv hsm).continuous
  have hK : IsCompact (Metric.closedBall t0 1 ×ˢ uIcc (0 : ℝ) L) :=
    (isCompact_closedBall t0 1).prod isCompact_uIcc
  have hGU := hK.uniformContinuousOn_of_continuous hGc.continuousOn
  have hDU := hK.uniformContinuousOn_of_continuous hDc.continuousOn
  have hεpos : 0 < η / (2 * (L + 1)) := div_pos hη (by linarith)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff.1 hGU _ hεpos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.uniformContinuousOn_iff.1 hDU _ hεpos
  refine ⟨min (min δ1 δ2) 1, lt_min (lt_min hδ1 hδ2) one_pos, fun {t} ht => ?_⟩
  have htd : dist t t0 < min δ1 δ2 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht1 : dist t t0 < 1 := lt_of_lt_of_le ht (min_le_right _ _)
  have hpt : ∀ x ∈ uIcc (0 : ℝ) L,
      ‖Φ t u0 x - Φ t0 u0 x‖ < η / (2 * (L + 1)) ∧
      ‖deriv (Φ t u0) x - deriv (Φ t0 u0) x‖ < η / (2 * (L + 1)) := by
    intro x hx
    have hmt : (t, x) ∈ Metric.closedBall t0 1 ×ˢ uIcc (0 : ℝ) L :=
      ⟨Metric.mem_closedBall.2 ht1.le, hx⟩
    have hm0 : (t0, x) ∈ Metric.closedBall t0 1 ×ˢ uIcc (0 : ℝ) L :=
      ⟨Metric.mem_closedBall_self zero_le_one, hx⟩
    have d1 : dist (t, x) (t0, x) < δ1 := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact lt_of_lt_of_le htd (min_le_left _ _)
    have d2 : dist (t, x) (t0, x) < δ2 := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact lt_of_lt_of_le htd (min_le_right _ _)
    have e1 := h1 _ hmt _ hm0 d1
    have e2 := h2 _ hmt _ hm0 d2
    rw [dist_eq_norm] at e1 e2
    exact ⟨e1, e2⟩
  set ε := η / (2 * (L + 1)) with hε
  have hε2 : ε ^ 2 * (4 * (L + 1) ^ 2) = η ^ 2 := by
    rw [hε]
    field_simp
    norm_num
  have hLε : L * ε ^ 2 * 4 ≤ η ^ 2 := by
    rw [← hε2]
    nlinarith [mul_nonneg (sq_nonneg ε) (by positivity : (0 : ℝ) ≤ L ^ 2 + L + 1)]
  have hg := smooth_sub (hper t) (hper t0)
  have hgc : Continuous (fun x => Φ t u0 x - Φ t0 u0 x) := hg.smooth.continuous
  have hdg : ∀ x, deriv (fun x => Φ t u0 x - Φ t0 u0 x) x =
      deriv (Φ t u0) x - deriv (Φ t0 u0) x := fun x =>
    deriv_sub ((hper t).smooth.differentiable (by simp) x)
      ((hper t0).smooth.differentiable (by simp) x)
  have hcoef : ∀ n, (smH1 (hper t) - smH1 (hper t0)).val n =
      coeff L (liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) n := by
    intro n
    rw [WSeq.val_sub, Pi.sub_apply, smH1_val', smH1_val', coeff_liftC_eq hg n,
      cIntg_sub (hper t).smooth.continuous (hper t0).smooth.continuous n]
    ring
  have hs1 := hasSum_sq_coeff L (memLp_of_continuous (liftC hg.smooth.continuous hg.periodic : C(AddCircle L, ℂ)).continuous)
  rw [integral_addCircle_sq hg] at hs1
  have hs2 := hasSum_kinetic hg
  have hsum := hs1.add hs2
  have hnorm : ‖smH1 (hper t) - smH1 (hper t0)‖ ^ 2 =
      (∫ x in (0 : ℝ)..L, ‖Φ t u0 x - Φ t0 u0 x‖ ^ 2) +
        ∫ x in (0 : ℝ)..L, ‖deriv (fun x => Φ t u0 x - Φ t0 u0 x) x‖ ^ 2 := by
    rw [h04_norm_sq]
    unfold f04NormSq
    have hfun : (fun n : ℤ => f04Weight L 1 n * ‖(smH1 (hper t) - smH1 (hper t0)).val n‖ ^ 2) =
        fun n : ℤ => ‖coeff L (liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) n‖ ^ 2 +
          freq L n ^ 2 * ‖coeff L (liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) n‖ ^ 2 := by
      funext n
      rw [hcoef n, f04Weight, Real.rpow_one]
      ring
    rw [hfun, hsum.tsum_eq]
  have hI1 : ∫ x in (0 : ℝ)..L, ‖Φ t u0 x - Φ t0 u0 x‖ ^ 2 ≤ L * ε ^ 2 := by
    have hf : IntervalIntegrable (fun x => ‖Φ t u0 x - Φ t0 u0 x‖ ^ 2) volume 0 L :=
      ((continuous_norm.comp hgc).pow 2).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on (f := fun x => ‖Φ t u0 x - Φ t0 u0 x‖ ^ 2)
      (g := fun _ => ε ^ 2) (le_of_lt hLpos) hf intervalIntegrable_const
      (fun x hx => by
        show ‖Φ t u0 x - Φ t0 u0 x‖ ^ 2 ≤ ε ^ 2
        have h := (hpt x (Icc_subset_uIcc hx)).1
        have h0 : 0 ≤ ‖Φ t u0 x - Φ t0 u0 x‖ := norm_nonneg _
        nlinarith)
    simpa using this
  have hI2 : ∫ x in (0 : ℝ)..L, ‖deriv (fun x => Φ t u0 x - Φ t0 u0 x) x‖ ^ 2 ≤ L * ε ^ 2 := by
    have hf : IntervalIntegrable (fun x => ‖deriv (fun x => Φ t u0 x - Φ t0 u0 x) x‖ ^ 2) volume 0 L :=
      ((continuous_norm.comp (deriv_continuous hg)).pow 2).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on
      (f := fun x => ‖deriv (fun x => Φ t u0 x - Φ t0 u0 x) x‖ ^ 2)
      (g := fun _ => ε ^ 2) (le_of_lt hLpos) hf intervalIntegrable_const
      (fun x hx => by
        show ‖deriv (fun x => Φ t u0 x - Φ t0 u0 x) x‖ ^ 2 ≤ ε ^ 2
        rw [hdg x]
        have h := (hpt x (Icc_subset_uIcc hx)).2
        have h0 : 0 ≤ ‖deriv (Φ t u0) x - deriv (Φ t0 u0) x‖ := norm_nonneg _
        nlinarith)
    simpa using this
  have hsq : ‖smH1 (hper t) - smH1 (hper t0)‖ ^ 2 < η ^ 2 := by
    rw [hnorm]
    have := pow_pos hη 2
    linarith
  have hlt : ‖smH1 (hper t) - smH1 (hper t0)‖ < η := by
    nlinarith [norm_nonneg (smH1 (hper t) - smH1 (hper t0))]
  rw [dist_eq_norm]
  exact hlt

/-! ## 7. Coefficients determine continuous profiles -/

theorem eq_of_coeff_eq {F G : AddCircle L → ℂ} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ n, coeff L F n = coeff L G n) : F = G := by
  have hint : ∀ (H : AddCircle L → ℂ), Continuous H → ∀ n : ℤ,
      Integrable (fun x => conj (mode L n x) * H x) (volume : Measure (AddCircle L)) := by
    intro H hH n
    exact ((Complex.continuous_conj.comp (continuous_mode n)).mul hH).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsub : ∀ n, coeff L (fun x => F x - G x) n = 0 := by
    intro n
    have e := h n
    unfold coeff at e ⊢
    simp only [mul_sub]
    rw [integral_sub (hint F hF n) (hint G hG n), e, sub_self]
  have hH : Continuous (fun x => F x - G x) := hF.sub hG
  have hcoef : coeff L (fun x => F x - G x) = fun _ => 0 := funext hsub
  have hmem : Mem04 L 1 (coeff L (fun x => F x - G x)) := by
    rw [hcoef]
    simp [Mem04]
  have hae := ae_eq_seriesRep (memLp_of_continuous hH) hmem
  rw [hcoef] at hae
  have hz : seriesRep L (fun _ => (0 : ℂ)) = fun _ => 0 := by
    funext x
    simp [seriesRep]
  rw [hz] at hae
  have hHz : (fun x => F x - G x) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq volume hH continuous_const).1 hae
  funext x
  exact sub_eq_zero.1 (congrFun hHz x)

/-! ## 8. The flow of `Re I_3` is a distributional solution in `h^1` -/

theorem smH1_congr {u v : ℝ → ℂ} (hu : SmoothPeriodic L u) (hv : SmoothPeriodic L v) (h : u = v) :
    smH1 hu = smH1 hv := by
  subst h
  rfl

set_option maxHeartbeats 1000000 in
theorem weak_flow {κ : ℝ} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} {u0 : ℝ → ℂ}
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u0 p.2))
    (hper : ∀ s, SmoothPeriodic L (Φ s u0))
    (hpde : ∀ s x, HasDerivAt (fun s' => Φ s' u0 x) (-Complex.I * cubicGrad κ (Φ s u0) x) s)
    (n : ℤ) (φ : ℝ → ℝ) (hφ : IsTest univ φ) :
    -Complex.I * ∫ t, deriv φ t • (smH1 (hper t)).val n =
      ∫ t, φ t • (((freq L n ^ 2 : ℝ) : ℂ) * (smH1 (hper t)).val n +
        ((2 * κ : ℝ) : ℂ) * (Fh (le_refl (1 : ℝ)) (smH1 (hper t))).val n) := by
  have hODE : ∀ t, HasDerivAt (fun s => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (Φ s u0) n)
      (-Complex.I * (((freq L n ^ 2 : ℝ) : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (Φ t u0) n) +
        ((2 * κ : ℝ) : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (nlCub (Φ t u0)) n))) t :=
    fun t => ((hasDerivAt_cIntg hsm hper hpde n t).const_mul _).congr_deriv (by ring)
  have hAc : Continuous fun s => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (Φ s u0) n :=
    continuous_const.mul (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_cIntg hsm hper hpde n t).continuousAt)
  have hNL : Continuous (fun p : ℝ × ℝ => nlCub (Φ p.1 u0) p.2) := by
    unfold nlCub
    exact (Complex.continuous_ofReal.comp ((continuous_norm.comp hsm.continuous).pow 2)).mul
      hsm.continuous
  have hPar : Continuous fun s => ∫ x in (0 : ℝ)..L, chi L n x * nlCub (Φ s u0) x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun s x => chi L n x * nlCub (Φ s u0) x)
      (((chi_continuous n).comp continuous_snd).mul hNL) 0 L
  have hBc : Continuous fun s => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (nlCub (Φ s u0)) n :=
    continuous_const.mul hPar
  have key := weak_of_ode (lam := ((freq L n ^ 2 : ℝ) : ℂ)) (mu := ((2 * κ : ℝ) : ℂ))
    hODE hAc hBc hφ
  have hv : ∀ t, (smH1 (hper t)).val n =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (Φ t u0) n := fun t => smH1_val' (hper t) n
  have hF : ∀ t, (Fh (le_refl (1 : ℝ)) (smH1 (hper t))).val n =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * cIntg L (nlCub (Φ t u0)) n :=
    fun t => Fh_val_smH1 (hper t) n
  simp only [hv, hF]
  exact key

/-- **Distributional form.** For a Hamiltonian flow `Φ` of `Re I_3` through `u₀`, the curve
`t ↦ smH1 (Φ_t u₀)` in `h^1` is an `IsDistSol κ univ` (κ arbitrary here). -/
theorem isDistSol_of_flow {κ : ℝ} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} {u0 : ℝ → ℂ}
    (hsm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u0 p.2))
    (hper : ∀ s, SmoothPeriodic L (Φ s u0))
    (hpde : ∀ s x, HasDerivAt (fun s' => Φ s' u0 x) (-Complex.I * cubicGrad κ (Φ s u0) x) s) :
    IsDistSol κ univ (fun t => smH1 (hper t)) :=
  ⟨isOpen_univ, Set.ordConnected_univ, (continuous_smH1 hsm hper).continuousOn,
    fun n φ hφ => weak_flow hsm hper hpde n φ hφ⟩

/-! ## 9. Uniqueness of the order-2 Hamiltonian flow (κ ≥ 0) -/

/-- **D1 (UniqueHamFlow at r = 2).** For `κ ≥ 0` and any Hamiltonian flow `Φ` of `Re I_3`, every
Hamiltonian flow `Ψ` of `Re I_3` agrees with `Φ` on smooth periodic data. -/
theorem unique_two {κ : ℝ} (hκ : 0 ≤ κ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 2) Φ) :
    UniqueHamFlow L (hamiltonian L κ 2) Φ := by
  intro Ψ hΨ u hu s
  have hL : 0 < L := Fact.out
  obtain ⟨h0Φ, hsmΦ, hsΦ⟩ := (isHamFlow_two_iff hL κ Φ).1 hΦ u hu
  obtain ⟨h0Ψ, hsmΨ, hsΨ⟩ := (isHamFlow_two_iff hL κ Ψ).1 hΨ u hu
  have hD1 := isDistSol_of_flow hsmΦ (fun t => (hsΦ t).1) (fun t x => (hsΦ t).2 x)
  have hD2 := isDistSol_of_flow hsmΨ (fun t => (hsΨ t).1) (fun t x => (hsΨ t).2 x)
  have h0 : smH1 (hsΦ 0).1 = smH1 (hsΨ 0).1 :=
    smH1_congr (hsΦ 0).1 (hsΨ 0).1 (h0Φ.trans h0Ψ.symm)
  have hfin := dist_unique hκ hD1 hD2 (Set.mem_univ (0 : ℝ)) h0 s (Set.mem_univ s)
  have hEq : (liftC (hsΦ s).1.smooth.continuous (hsΦ s).1.periodic : AddCircle L → ℂ) =
      (liftC (hsΨ s).1.smooth.continuous (hsΨ s).1.periodic : AddCircle L → ℂ) :=
    eq_of_coeff_eq (liftC (hsΦ s).1.smooth.continuous (hsΦ s).1.periodic).continuous
      (liftC (hsΨ s).1.smooth.continuous (hsΨ s).1.periodic).continuous
      (fun n => congrArg (fun a : h04 L 1 => a.val n) hfin)
  funext x
  have hx := congrFun hEq (x : AddCircle L)
  rw [liftC_coe, liftC_coe] at hx
  exact hx.symm

#print axioms smH1_val'
#print axioms Fh_val_smH1
#print axioms integral_chi_cubicGrad
#print axioms hasDerivAt_cIntg
#print axioms weak_of_ode
#print axioms continuous_smH1
#print axioms eq_of_coeff_eq
#print axioms weak_flow
#print axioms isDistSol_of_flow
#print axioms unique_two

end QuantumNLS.Def024CubicUnique
