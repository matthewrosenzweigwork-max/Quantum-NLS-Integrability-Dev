import Mathlib
import QuantumNLS.RootPlacementBound
import QuantumNLS.NormalizedTransfer
import QuantumNLS.MixedCommutator

/-!
# The factorial kernel bound `eq:MP-kernel` / `Q7A:eq:kernels` for the realized DEF-048 kernels

Sources: `source/chapters/foundations/periodic_basis.tex` (`basis:eq:kernelbound`, "the simplex volume and the phase
lengths in `[0,L]` imply `‖K_{m,z}‖ ≤ 2e^{L|Im z|}L^m/√((2m)!)`"), the Hilbert-Schmidt proof of
`lem:A30-entire-bound` (`source/chapters/hierarchy_laws/quantum_law_bridge.tex`: "supported on ordered simplices in `2r`
variables, each of volume `L^{2r}/(2r)!`; the exponential has modulus `≤ e^{L|Im z|/2}` ...; the Hilbert-Schmidt norm of each
unsymmetrized kernel is at most `...L^r/√(2r)!`; orthogonal projections do not increase it"), and its use as
`mixed_propagation.tex` `eq:MP-kernel` and `window_reconstruction.tex` `Q7A:eq:kernels` (the latter lists it among the
model hypotheses).  Imports read-only: `RootPlacementBound` (Schur/torus tools, `norm_positionInclusion_le`),
`NormalizedTransfer` (DEF-048 `orderedKernel = physicalKernel`), `BetheTransferOperators`/`BetheIntegralOperator`
(the frozen `Kernel` and its `operator`), and `MixedCommutator` (for the restated PROP-026).

## Proved
* **Hilbert-Schmidt bound for the frozen integral operators** (`norm_form_le_hs`, `norm_operator_le_hs`): for the
  repository's `BetheIntegralOperator.Kernel μ` (bounded measurable kernel, `operator` constructed by Riesz duality),
  `∫∫|k|² ≤ c²` (`c > 0`) implies `‖operator‖ ≤ c` (Cauchy-Schwarz via `|k||f||g| ≤ ½(t|k|² + |f|²|g|²/t)`).  Mathlib has no
  such inequality for this operator form; it is proved here.
* **The factorial simplex volume** (`card_factorial_mul_volume_chain_le`, `factorial_mul_volume_plusOrder_le`): the `n!`
  coordinate permutations of the chain `{L>t_1>…>t_n>0}` are pairwise disjoint subsets of `(0,L)^n`, so
  `n! · vol ≤ L^n`; for the alternating chamber `L>x_1>y_1>…>x_m>y_m>0` (`PlusOrder`), `(2m)! · vol ≤ L^{2m}`.  (An upper
  bound suffices; it is the whole content of "volume `L^{2r}/(2r)!`".)
* **Kernel Hilbert-Schmidt integral and operator bounds** (`kernel_hs_le`, `norm_plusKernel_le_fact`,
  `norm_minusKernel_le_fact`, `norm_rawOperator_le_fact`): `∫∫|K̃^±|² ≤ e^{2L|Im z|}L^{2m}/(2m)!`, using the realized chamber
  moduli `norm_rawPlus_le`/`norm_rawMinus_le` (`≤ e^{L|Im z|}`, all of `z ∈ ℂ`), hence `‖K̃^±_{m,z}‖ ≤ e^{L|Im z|}L^m/√((2m)!)`
  and `‖K̃⁺+K̃⁻‖ ≤ 2 e^{L|Im z|}L^m/√((2m)!)`.
* **`norm_physicalKernel_le_fact`**: `‖K_{r,z}‖ = ‖P_r(K̃⁺+K̃⁻)P_r‖ ≤ 2e^{L|Im z|}L^r/√((2r)!)` for the realized
  `physicalKernel L r z` (the compression by the position inclusion is contractive), every `r` and `z ∈ ℂ`.
* **`kernel_bound`** (the printed `eq:MP-kernel`, `Q7A:eq:kernels`): `|κ|^r ‖orderedKernel L r z‖ ≤ 2e^{L|Im z|}(|κ|L)^r/√((2r)!)`.
  This also supplies the factorial bound that the PROP-008 consumers (e.g. `HighMomentsRank`, `fluctuations.tex:17`) take as input.
* **`prop026_traceNorm_transfer_sharp`**: `MixedCommutator.prop026_traceNorm_transfer` with the kernel hypothesis `hker`
  DISCHARGED by `kernel_bound` (it holds for all `w ∈ ℂ`).  Same constant `C_J`.  The only remaining non-structural
  hypothesis is `hquad`: that each `Φ θ (coordC j)` is a quadrature `α S_N(z_θ) + β S_N(z_θ)^*`, `‖α‖+‖β‖ ≤ 1`, of the realized
  `normalizedTransfer` at a point of the strip `|Im z| ≤ h` (PROP-026 remainder 3).  As before, the PROP-014 operator-norm
  Bochner convention is inherited as an explicitly labelled interpretation, not an owner ruling.

## Notes
* `κ^j` is read as `|κ|^j` (identical for `κ > 0`).  The bound holds without any sign or size assumption on `z`.
* Not proved here: remainder 3 (identification of the abstract `Φ θ` with `Re/Im S_N(z_θ)`, i.e. `hquad`, and the
  chart/`D, A, s, G` objects), and the sharper `r`-dependence beyond the printed one.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace BigOperators Nat ContDiff

noncomputable section

namespace QuantumNLS.KernelFactorialBound

open QuantumNLS.BetheIntegralOperator QuantumNLS.RootPlacementBound

/-! ### A. The Hilbert-Schmidt bound for the frozen bounded integral operators -/

section HS

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_kernel_sq (k : Kernel μ) : Integrable (fun p => ‖k.fn p‖ ^ 2) (μ.prod μ) := by
  refine (integrable_const (k.bound ^ 2)).mono' (k.measurable.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (k.norm_le p) 2

/-- **Cauchy-Schwarz form of the Hilbert-Schmidt bound.** -/
theorem norm_form_le_hs (k : Kernel μ) {c : ℝ} (hc : 0 < c)
    (hA : ∫ p, ‖k.fn p‖ ^ 2 ∂(μ.prod μ) ≤ c ^ 2) (f g : H μ) :
    ‖k.form f g‖ ≤ c * ‖f‖ * ‖g‖ := by
  by_cases h0 : ‖f‖ * ‖g‖ = 0
  · have := k.norm_form_le f g
    have h1 : (k.bound * ‖oneVector μ‖ ^ 2) * ‖f‖ * ‖g‖ = 0 := by
      rw [mul_assoc, h0, mul_zero]
    have h2 : c * ‖f‖ * ‖g‖ = 0 := by rw [mul_assoc, h0, mul_zero]
    rw [h2]
    linarith
  · have hP : 0 < ‖f‖ * ‖g‖ :=
      lt_of_le_of_ne (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm h0)
    set P : ℝ := ‖f‖ * ‖g‖ with hPdef
    set t : ℝ := P / c with htdef
    have ht : 0 < t := div_pos hP hc
    have hf2 := integrable_norm_sq f
    have hg2 := integrable_norm_sq g
    have hfg : Integrable (fun p : X × X => ‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2) (μ.prod μ) :=
      hf2.mul_prod hg2
    have hk := integrable_kernel_sq k
    have hbd : Integrable (fun p : X × X =>
        (t * ‖k.fn p‖ ^ 2 + (‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2) / t) / 2) (μ.prod μ) :=
      ((hk.const_mul t).add (hfg.div_const t)).div_const 2
    have hI : ∫ p, (‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2) ∂(μ.prod μ) = P ^ 2 := by
      rw [integral_prod_mul (fun x => ‖f x‖ ^ 2) (fun x => ‖g x‖ ^ 2),
        integral_norm_sq_eq, integral_norm_sq_eq, hPdef]
      ring
    calc ‖k.form f g‖
        ≤ ∫ p, (t * ‖k.fn p‖ ^ 2 + (‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2) / t) / 2 ∂(μ.prod μ) := by
          apply norm_integral_le_of_norm_le hbd
          filter_upwards with p
          simp only [Kernel.integrand, norm_mul, Complex.norm_conj]
          set a := ‖k.fn p‖
          set b := ‖f p.1‖ * ‖g p.2‖ with hb
          have e1 : ‖f p.1‖ * a * ‖g p.2‖ = a * b := by rw [hb]; ring
          have e2 : ‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2 = b ^ 2 := by rw [hb]; ring
          rw [e1, e2]
          have : t * a ^ 2 + b ^ 2 / t - 2 * (a * b) = (t * a - b) ^ 2 / t := by
            field_simp
            ring
          have h3 : 0 ≤ (t * a - b) ^ 2 / t := by positivity
          linarith
      _ = (t * ∫ p, ‖k.fn p‖ ^ 2 ∂(μ.prod μ) + P ^ 2 / t) / 2 := by
          rw [integral_div, integral_add (hk.const_mul t) (hfg.div_const t), integral_const_mul,
            integral_div, hI]
      _ ≤ (t * c ^ 2 + P ^ 2 / t) / 2 := by
          have := mul_le_mul_of_nonneg_left hA ht.le
          linarith
      _ = c * P := by
          rw [htdef]
          field_simp
          ring
      _ = c * ‖f‖ * ‖g‖ := by rw [hPdef]; ring

/-- **Hilbert-Schmidt bound**: `‖T_k‖ ≤ c` whenever `∫∫|k|² ≤ c²`, `c > 0`. -/
theorem norm_operator_le_hs (k : Kernel μ) {c : ℝ} (hc : 0 < c)
    (hA : ∫ p, ‖k.fn p‖ ^ 2 ∂(μ.prod μ) ≤ c ^ 2) : ‖k.operator‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun g => ?_
  have hb := norm_form_le_hs k hc hA (k.operator g) g
  rw [← Kernel.inner_operator, inner_self_eq_norm_sq_to_K] at hb
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at hb
  by_cases hz : ‖k.operator g‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖k.operator g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have : ‖k.operator g‖ * ‖k.operator g‖ ≤ ‖k.operator g‖ * (c * ‖g‖) := by nlinarith
    exact le_of_mul_le_mul_left this hp

end HS

/-! ### B. The factorial volume of an ordered chain -/

section Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem perm_eq_one_of_keyMono (κ : ι → ℕ) (hκ : Function.Injective κ) (ρ : Equiv.Perm ι)
    (h : ∀ a b, κ a < κ b → κ (ρ a) < κ (ρ b)) : ρ = 1 := by
  letI : LinearOrder ι := LinearOrder.lift' κ hκ
  have hs : StrictMono ρ := fun a b hab => h a b hab
  have h1 := Subsingleton.elim (hs.orderIsoOfSurjective ρ ρ.surjective) (OrderIso.refl ι)
  ext a
  have h2 := congrArg (fun e : ι ≃o ι => e a) h1
  simpa using h2

/-- The set of `t : ι → ℝ` with values in `(0,L)` that are strictly decreasing along the key `κ`. -/
def chainSet (L : ℝ) (κ : ι → ℕ) : Set (ι → ℝ) :=
  {t | (∀ a, t a ∈ Ioo 0 L) ∧ ∀ a b, κ a < κ b → t b < t a}

theorem measurableSet_chainSet (L : ℝ) (κ : ι → ℕ) : MeasurableSet (chainSet L κ) := by
  have h1 : MeasurableSet {t : ι → ℝ | ∀ a, t a ∈ Ioo 0 L} := by
    have : {t : ι → ℝ | ∀ a, t a ∈ Ioo 0 L} = Set.pi univ fun _ => Ioo 0 L := by
      ext t; simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have h2 : MeasurableSet {t : ι → ℝ | ∀ a b, κ a < κ b → t b < t a} := by
    have : {t : ι → ℝ | ∀ a b, κ a < κ b → t b < t a} =
        ⋂ a, ⋂ b, {t | κ a < κ b → t b < t a} := by
      ext t; simp
    rw [this]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
    by_cases hab : κ a < κ b
    · simp only [hab, true_implies]
      exact measurableSet_lt (measurable_pi_apply b) (measurable_pi_apply a)
    · simp [hab]
  exact h1.inter h2

/-- **`(card ι)! · vol(chain) ≤ L^{card ι}`**: the `n!` coordinate permutations of an ordered chain are
pairwise disjoint subsets of the cube. -/
theorem card_factorial_mul_volume_chain_le (L : ℝ) (κ : ι → ℕ) (hκ : Function.Injective κ) :
    ((Fintype.card ι)! : ENNReal) * volume (chainSet L κ) ≤ ENNReal.ofReal L ^ Fintype.card ι := by
  set T := chainSet L κ with hT
  let perm : Equiv.Perm ι → Set (ι → ℝ) := fun σ => (fun t : ι → ℝ => t ∘ σ) ⁻¹' T
  have hmp : ∀ σ : Equiv.Perm ι, MeasurePreserving (fun t : ι → ℝ => t ∘ σ) volume volume := by
    intro σ
    have h := volume_preserving_arrowCongr' (α₁ := ι) (α₂ := ι) (β₁ := ℝ) (β₂ := ℝ) σ.symm
      (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
    convert h using 1
    funext t i
    simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
  have hmeas : ∀ σ : Equiv.Perm ι, MeasurableSet (perm σ) := fun σ =>
    (measurableSet_chainSet L κ).preimage (hmp σ).measurable
  have hvol : ∀ σ : Equiv.Perm ι, volume (perm σ) = volume T := by
    intro σ
    exact (hmp σ).measure_preimage (measurableSet_chainSet L κ).nullMeasurableSet
  have hdisj : Pairwise (Function.onFun Disjoint perm) := by
    intro σ τ hστ
    refine Set.disjoint_left.2 fun t h1 h2 => hστ ?_
    obtain ⟨-, h1'⟩ := h1
    obtain ⟨-, h2'⟩ := h2
    have hρ : (σ.trans τ.symm) = 1 := by
      apply perm_eq_one_of_keyMono κ hκ
      intro a b hab
      by_contra hn
      have hne : κ ((σ.trans τ.symm) a) ≠ κ ((σ.trans τ.symm) b) := by
        intro he
        have := (σ.trans τ.symm).injective (hκ he)
        exact (ne_of_lt hab) (by rw [this])
      have hlt : κ ((σ.trans τ.symm) b) < κ ((σ.trans τ.symm) a) :=
        lt_of_le_of_ne (not_lt.1 hn) (Ne.symm hne)
      have e1 := h2' _ _ hlt
      have e2 := h1' a b hab
      have ea : τ ((σ.trans τ.symm) a) = σ a := by simp
      have eb : τ ((σ.trans τ.symm) b) = σ b := by simp
      simp only [Function.comp_apply, ea, eb] at e1 e2
      linarith
    ext a
    have := congrArg (fun e : Equiv.Perm ι => e a) hρ
    simp at this
    exact (τ.symm_apply_eq.mp this)
  have hsub : (⋃ σ, perm σ) ⊆ Set.pi univ fun _ => Ioo (0 : ℝ) L := by
    intro t ht
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 ht
    intro a _
    have := hσ.1 (σ.symm a)
    simpa using this
  have hsum : ∑ σ : Equiv.Perm ι, volume (perm σ) = volume (⋃ σ, perm σ) := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype]
  calc ((Fintype.card ι)! : ENNReal) * volume T
      = ∑ σ : Equiv.Perm ι, volume (perm σ) := by
        simp only [hvol, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
    _ = volume (⋃ σ, perm σ) := hsum
    _ ≤ volume (Set.pi univ fun _ : ι => Ioo (0 : ℝ) L) := measure_mono hsub
    _ = ENNReal.ofReal L ^ Fintype.card ι := by
        rw [Real.volume_pi_Ioo]
        simp

end Simplex

/-! ### C. The Hilbert-Schmidt integral of the alternating-chamber kernels -/

section Chamber

open QuantumNLS.BetheTransferKernelAdjoint QuantumNLS.BetheTransferOperators
  QuantumNLS.BetheWeakGradient QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)] {m : ℕ}

/-- Torus integrals of functions of the representatives become cube integrals, on pairs. -/
theorem integral_prod_representatives (F : (Fin m → ℝ) × (Fin m → ℝ) → ℝ) (hF : Measurable F)
    (C : ℝ) (hC : ∀ q, ‖F q‖ ≤ C) :
    ∫ p, F (representatives L p.1, representatives L p.2)
        ∂(torusPiMeasure L m).prod (torusPiMeasure L m) =
      ∫ q, F q ∂(cubeMeasure m L).prod (cubeMeasure m L) := by
  have hR : Measurable fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
      (representatives L p.1, representatives L p.2) :=
    ((measurable_representatives m L).comp measurable_fst).prodMk
      ((measurable_representatives m L).comp measurable_snd)
  have hint1 : Integrable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
      F (representatives L p.1, representatives L p.2))
      ((torusPiMeasure L m).prod (torusPiMeasure L m)) :=
    (integrable_const C).mono' (hF.comp hR).aestronglyMeasurable (ae_of_all _ fun p => hC _)
  have hint2 : Integrable F ((cubeMeasure m L).prod (cubeMeasure m L)) :=
    (integrable_const C).mono' hF.aestronglyMeasurable (ae_of_all _ hC)
  rw [integral_prod _ hint1, integral_prod _ hint2]
  have hinner : ∀ x : Fin m → AddCircle L,
      ∫ y, F (representatives L x, representatives L y) ∂torusPiMeasure L m =
        ∫ y', F (representatives L x, y') ∂cubeMeasure m L := fun x =>
    torus_real_integral L (fun y' => F (representatives L x, y'))
      (hF.comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  have hm : Measurable fun x' : Fin m → ℝ => ∫ y', F (x', y') ∂cubeMeasure m L :=
    (hF.stronglyMeasurable.integral_prod_right').measurable
  exact torus_real_integral L (fun x' => ∫ y', F (x', y') ∂cubeMeasure m L) hm

/-- **Hilbert-Schmidt integral of a kernel dominated by a chamber indicator.** -/
theorem kernel_hs_le (k : Kernel (torusPiMeasure L m)) (E : ℝ) (hE : 0 ≤ E)
    (S : Set ((Fin m → ℝ) × (Fin m → ℝ))) (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hk : ∀ x y, ‖k.fn (x, y)‖ ≤
      E * S.indicator (fun _ => (1 : ℝ)) (representatives L x, representatives L y)) :
    ∫ p, ‖k.fn p‖ ^ 2 ∂(torusPiMeasure L m).prod (torusPiMeasure L m) ≤
      E ^ 2 * (volume S).toReal := by
  set G : (Fin m → ℝ) × (Fin m → ℝ) → ℝ := fun q => (E * S.indicator (fun _ => (1 : ℝ)) q) ^ 2
    with hG
  have hGm : Measurable G :=
    ((measurable_const.indicator hS).const_mul E).pow_const 2
  have hGb : ∀ q, ‖G q‖ ≤ E ^ 2 := by
    intro q
    rw [hG]
    simp only [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_nonneg hE]
    have : |S.indicator (fun _ => (1 : ℝ)) q| ≤ 1 := by
      by_cases hq : q ∈ S <;> simp [hq]
    calc (E * |S.indicator (fun _ => (1 : ℝ)) q|) ^ 2 ≤ (E * 1) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left this hE
      _ = E ^ 2 := by ring
  have hR : Measurable fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
      (representatives L p.1, representatives L p.2) :=
    ((measurable_representatives m L).comp measurable_fst).prodMk
      ((measurable_representatives m L).comp measurable_snd)
  have hint1 : Integrable (fun p : (Fin m → AddCircle L) × (Fin m → AddCircle L) =>
      G (representatives L p.1, representatives L p.2))
      ((torusPiMeasure L m).prod (torusPiMeasure L m)) :=
    (integrable_const (E ^ 2)).mono' (hGm.comp hR).aestronglyMeasurable
      (ae_of_all _ fun p => hGb _)
  calc ∫ p, ‖k.fn p‖ ^ 2 ∂(torusPiMeasure L m).prod (torusPiMeasure L m)
      ≤ ∫ p, G (representatives L p.1, representatives L p.2)
          ∂(torusPiMeasure L m).prod (torusPiMeasure L m) := by
        refine integral_mono (integrable_kernel_sq k) hint1 fun p => ?_
        rw [hG]
        exact pow_le_pow_left₀ (norm_nonneg _) (hk p.1 p.2) 2
    _ = ∫ q, G q ∂(cubeMeasure m L).prod (cubeMeasure m L) :=
        integral_prod_representatives G hGm (E ^ 2) hGb
    _ = ∫ q, (E ^ 2) * S.indicator (fun _ => (1 : ℝ)) q
          ∂(cubeMeasure m L).prod (cubeMeasure m L) := by
        refine integral_congr_ae (ae_of_all _ fun q => ?_)
        rw [hG]
        by_cases hq : q ∈ S <;> simp [hq]
    _ = E ^ 2 * ((cubeMeasure m L).prod (cubeMeasure m L)).real S := by
        rw [integral_const_mul, integral_indicator_const _ hS, smul_eq_mul, mul_one]
    _ ≤ E ^ 2 * (volume S).toReal := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hle : (cubeMeasure m L).prod (cubeMeasure m L) ≤ volume := by
          rw [Measure.volume_eq_prod, cubeMeasure]
          calc (volume.restrict (Icc (fun _ : Fin m => (0 : ℝ)) fun _ => L)).prod
                (volume.restrict (Icc (fun _ : Fin m => (0 : ℝ)) fun _ => L))
              = (volume.prod volume).restrict (_ ×ˢ _) := Measure.prod_restrict _ _
            _ ≤ volume.prod volume := Measure.restrict_le_self
        exact ENNReal.toReal_mono hSfin (hle S)

end Chamber

/-! ### D. Volume of the alternating chamber and the factorial kernel bound -/

section Factorial

open QuantumNLS.BetheTransferKernelAdjoint QuantumNLS.BetheTransferOperators
  QuantumNLS.BetheWeakGradient QuantumNLS.PhysicalTensor

/-- The key of the alternating chain `x₁>y₁>x₂>y₂>…`: `x_j ↦ 2j`, `y_j ↦ 2j+1`. -/
def chainKey (m : ℕ) : Fin m ⊕ Fin m → ℕ
  | Sum.inl j => 2 * j.val
  | Sum.inr j => 2 * j.val + 1

theorem chainKey_injective (m : ℕ) : Function.Injective (chainKey m) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp only [chainKey] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem plusOrder_subset_chain (L : ℝ) (m : ℕ) (t : Fin m ⊕ Fin m → ℝ)
    (h : PlusOrder L (fun j => t (Sum.inl j)) (fun j => t (Sum.inr j))) :
    t ∈ chainSet L (chainKey m) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro a
    rcases a with a | a
    · obtain ⟨u1, u2, u3⟩ := h1 a
      exact ⟨u1.trans u2, u3⟩
    · obtain ⟨u1, u2, u3⟩ := h1 a
      exact ⟨u1, u2.trans u3⟩
  · intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [chainKey] at hab
    · have hij : a < b := by rw [Fin.lt_def]; omega
      exact (h2 a b hij).trans (h1 a).2.1
    · -- x_a > y_b
      rcases (show a ≤ b by rw [Fin.le_def]; omega).eq_or_lt with hh | hh
      · subst hh; exact (h1 a).2.1
      · exact lt_trans (h1 b).2.1 (lt_trans (h2 a b hh) (h1 a).2.1)
    · have hij : a < b := by rw [Fin.lt_def]; omega
      exact h2 a b hij
    · have hij : a < b := by rw [Fin.lt_def]; omega
      exact ((h1 b).2.1).trans (h2 a b hij)

variable {L : ℝ} [Fact (0 < L)] (m : ℕ)

/-- **The simplex volume bound**: `(2m)! · vol{(x,y) : L>x₁>y₁>…>x_m>y_m>0} ≤ L^{2m}`. -/
theorem factorial_mul_volume_plusOrder_le :
    ((m + m)! : ENNReal) *
      volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} ≤
        ENNReal.ofReal L ^ (m + m) := by
  set S : Set ((Fin m → ℝ) × (Fin m → ℝ)) := {p | PlusOrder L p.1 p.2} with hS
  set e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin m => ℝ) with he
  have hmp : MeasurePreserving e volume volume := volume_measurePreserving_sumPiEquivProdPi _
  have hSm : MeasurableSet S := measurableSet_plusOrder m L
  have hvol : volume S = volume (e ⁻¹' S) := (hmp.measure_preimage hSm.nullMeasurableSet).symm
  have hsub : e ⁻¹' S ⊆ chainSet L (chainKey m) := by
    intro t ht
    exact plusOrder_subset_chain L m t ht
  have h1 := card_factorial_mul_volume_chain_le (ι := Fin m ⊕ Fin m) L (chainKey m)
    (chainKey_injective m)
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  calc ((m + m)! : ENNReal) * volume S = ((m + m)! : ENNReal) * volume (e ⁻¹' S) := by rw [hvol]
    _ ≤ ((m + m)! : ENNReal) * volume (chainSet L (chainKey m)) :=
        by gcongr
    _ ≤ _ := h1

theorem volume_plusOrder_ne_top :
    volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} ≠ ⊤ := by
  intro h
  have := factorial_mul_volume_plusOrder_le (L := L) m
  rw [h, ENNReal.mul_top (by exact_mod_cast (Nat.factorial_pos _).ne')] at this
  exact absurd this (by simp [top_le_iff, ENNReal.pow_eq_top_iff])

theorem volume_plusOrder_toReal_le :
    (volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2}).toReal ≤
      L ^ (m + m) / ((m + m)! : ℝ) := by
  have h := factorial_mul_volume_plusOrder_le (L := L) m
  have hne := volume_plusOrder_ne_top (L := L) m
  have h2 := ENNReal.toReal_mono (by simp [ENNReal.pow_eq_top_iff]) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Fact.out : 0 < L).le] at h2
  have hf : (0 : ℝ) < ((m + m)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [le_div_iff₀ hf]
  simpa [mul_comm] using h2

/-- The two chamber sets and their norms. -/
theorem volume_minusOrder_toReal_le :
    (volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1}).toReal ≤
      L ^ (m + m) / ((m + m)! : ℝ) := by
  have hsw : {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1} =
      Prod.swap ⁻¹' {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} := rfl
  have hswp : volume (Prod.swap ⁻¹' {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2}) =
      volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
      (ν := (volume : Measure (Fin m → ℝ)))).measure_preimage
      (measurableSet_plusOrder m L).nullMeasurableSet
    simpa [Measure.volume_eq_prod] using this
  rw [hsw, hswp]
  exact volume_plusOrder_toReal_le m

end Factorial

/-! ### E. The factorial bound for the realized DEF-048 kernels, and PROP-026 with `hker` discharged -/

section Final

open QuantumNLS.BetheTransferKernelAdjoint QuantumNLS.BetheTransferOperators
  QuantumNLS.BetheWeakGradient QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition

variable {L : ℝ} [Fact (0 < L)]

/-- The Hilbert-Schmidt constant `e^{L|Im z|} L^m / √((2m)!)`. -/
def hsConst (L : ℝ) (z : ℂ) (m : ℕ) : ℝ :=
  Real.exp (L * |z.im|) * L ^ m / Real.sqrt (((2 * m)! : ℕ) : ℝ)

theorem hsConst_pos (z : ℂ) (m : ℕ) : 0 < hsConst L z m := by
  have hL : 0 < L := Fact.out
  unfold hsConst
  positivity

theorem hsConst_sq (z : ℂ) (m : ℕ) :
    hsConst L z m ^ 2 = Real.exp (L * |z.im|) ^ 2 * (L ^ (m + m) / ((m + m)! : ℝ)) := by
  unfold hsConst
  have hf : (0 : ℝ) ≤ (((2 * m)! : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_pow, mul_pow, Real.sq_sqrt hf, ← pow_mul, two_mul, mul_comm m 2, two_mul]
  push_cast
  ring_nf

theorem volume_swap_plusOrder (m : ℕ) :
    volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1} =
      volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} := by
  have := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure (Fin m → ℝ)))).measure_preimage
    (measurableSet_plusOrder m L).nullMeasurableSet
  simpa [Measure.volume_eq_prod] using this

/-- **`‖K̃⁺_{m,z}‖ ≤ e^{L|Im z|} L^m/√((2m)!)`** (Hilbert-Schmidt norm of the ordered-simplex kernel). -/
theorem norm_plusKernel_le_fact (m : ℕ) (z : ℂ) :
    ‖(plusKernel L m z).operator‖ ≤ hsConst L z m := by
  refine norm_operator_le_hs _ (hsConst_pos z m) ?_
  refine (kernel_hs_le (plusKernel L m z) (Real.exp (L * |z.im|)) (Real.exp_pos _).le
    {p | PlusOrder L p.1 p.2} (measurableSet_plusOrder m L) (volume_plusOrder_ne_top m) ?_).trans ?_
  · intro x y
    change ‖rawPlus L z (representatives L x) (representatives L y)‖ ≤ _
    by_cases h : PlusOrder L (representatives L x) (representatives L y)
    · rw [Set.indicator_of_mem (show (representatives L x, representatives L y) ∈
        {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} from h), mul_one]
      exact norm_rawPlus_le L (Fact.out : 0 < L).le z _ _
    · have h0 : rawPlus L z (representatives L x) (representatives L y) = 0 := by
        simp [rawPlus, h]
      rw [h0, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · rw [hsConst_sq]
    exact mul_le_mul_of_nonneg_left (volume_plusOrder_toReal_le m) (by positivity)

theorem norm_minusKernel_le_fact (m : ℕ) (z : ℂ) :
    ‖(minusKernel L m z).operator‖ ≤ hsConst L z m := by
  refine norm_operator_le_hs _ (hsConst_pos z m) ?_
  have hsm : MeasurableSet {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1} :=
    (measurableSet_plusOrder m L).preimage measurable_swap
  have hfin : volume {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1} ≠ ⊤ := by
    rw [volume_swap_plusOrder]; exact volume_plusOrder_ne_top m
  refine (kernel_hs_le (minusKernel L m z) (Real.exp (L * |z.im|)) (Real.exp_pos _).le
    {p | PlusOrder L p.2 p.1} hsm hfin ?_).trans ?_
  · intro x y
    change ‖rawMinus L z (representatives L x) (representatives L y)‖ ≤ _
    by_cases h : PlusOrder L (representatives L y) (representatives L x)
    · rw [Set.indicator_of_mem (show (representatives L x, representatives L y) ∈
        {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.2 p.1} from h), mul_one]
      exact norm_rawMinus_le L (Fact.out : 0 < L).le z _ _
    · have h0 : rawMinus L z (representatives L x) (representatives L y) = 0 := by
        simp [rawMinus, MinusOrder, h]
      rw [h0, norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · rw [hsConst_sq]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact volume_minusOrder_toReal_le m

theorem norm_rawOperator_le_fact (m : ℕ) (z : ℂ) :
    ‖rawOperator L m z‖ ≤ 2 * hsConst L z m := by
  unfold rawOperator
  calc _ ≤ ‖(plusKernel L m z).operator‖ + ‖(minusKernel L m z).operator‖ := norm_add_le _ _
    _ ≤ hsConst L z m + hsConst L z m :=
        add_le_add (norm_plusKernel_le_fact m z) (norm_minusKernel_le_fact m z)
    _ = _ := by ring

/-- **`‖K_{r,z}‖ ≤ 2 e^{L|Im z|} L^r/√((2r)!)`** (`basis:eq:kernelbound`), for the realized physical kernels
`K_{r,z} = P_r(K̃⁺+K̃⁻)P_r`, every `r` and every `z ∈ ℂ`. -/
theorem norm_physicalKernel_le_fact (r : ℕ) (z : ℂ) :
    ‖QuantumNLS.BethePhysicalTransfer.physicalKernel L r z‖ ≤ 2 * hsConst L z r := by
  unfold QuantumNLS.BethePhysicalTransfer.physicalKernel
  have hP := norm_positionInclusion_le (L := L) r
  have hR := norm_rawOperator_le_fact (L := L) r z
  have hPa : ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L r).adjoint‖ ≤ 1 := by
    have : ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L r).adjoint‖ =
        ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L r‖ :=
      LinearIsometryEquiv.norm_map _ _
    rw [this]; exact hP
  have h2 := ContinuousLinearMap.opNorm_comp_le
    (QuantumNLS.BethePhysicalTransfer.positionInclusion L r).adjoint
    ((rawOperator L r z).comp (QuantumNLS.BethePhysicalTransfer.positionInclusion L r))
  have h3 := ContinuousLinearMap.opNorm_comp_le (rawOperator L r z)
    (QuantumNLS.BethePhysicalTransfer.positionInclusion L r)
  have hc := (hsConst_pos (L := L) z r).le
  calc _ ≤ ‖(QuantumNLS.BethePhysicalTransfer.positionInclusion L r).adjoint‖ *
        ‖(rawOperator L r z).comp (QuantumNLS.BethePhysicalTransfer.positionInclusion L r)‖ := h2
    _ ≤ 1 * (‖rawOperator L r z‖ * ‖QuantumNLS.BethePhysicalTransfer.positionInclusion L r‖) :=
        mul_le_mul hPa h3 (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ ≤ 1 * (2 * hsConst L z r * 1) := by gcongr
    _ = _ := by ring

/-- **`eq:MP-kernel` / `Q7A:eq:kernels`, proved for the realized DEF-048 kernels**:
`|κ|^r ‖K_{r,z}‖ ≤ 2 e^{L|Im z|} (|κ|L)^r/√((2r)!)`, for all `r`, `z`. -/
theorem kernel_bound (κ : ℝ) (r : ℕ) (z : ℂ) :
    |κ| ^ r * ‖orderedKernel L r z‖ ≤
      2 * Real.exp (L * |z.im|) * (|κ| * L) ^ r / Real.sqrt (((2 * r)! : ℕ) : ℝ) := by
  have h := norm_physicalKernel_le_fact (L := L) r z
  have hk : ‖orderedKernel L r z‖ ≤ 2 * hsConst L z r := h
  calc |κ| ^ r * ‖orderedKernel L r z‖ ≤ |κ| ^ r * (2 * hsConst L z r) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by
        unfold hsConst
        rw [mul_pow]
        ring

open MeasureTheory QuantumNLS.FunctionalLinearization in
/-- **PROP-026 (trace-norm form) with `hker` discharged**: `MixedCommutator.prop026_traceNorm_transfer` with the
kernel bound `eq:MP-kernel` PROVED (`kernel_bound`).  The remaining explicit hypothesis is `hquad`. -/
theorem prop026_traceNorm_transfer_sharp (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        (L : ℝ) [Fact (0 < L)] (κ : ℝ) (k q : ℕ) (hN : 1 ≤ k + q)
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ]
          (SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q)))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (phi : SymSector ℂ (L2T L) (k + q)) (hphi : ‖phi‖ = 1)
        (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hphiδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) •
          (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ δ θ)
        (z : Θ → ℂ) (h : ℝ) (hz : ∀ θ, |(z θ).im| ≤ h)
        (hquad : ∀ θ j, ∃ α β : ℂ, ‖α‖ + ‖β‖ ≤ 1 ∧
          Φ θ (coordC j) = α • normalizedTransfer L κ (k + q) (z θ) +
            β • (normalizedTransfer L κ (k + q) (z θ)).adjoint)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν)
        (hwδ : Integrable (fun θ => w θ * δ θ) ν)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        QuantumNLS.TraceClass.traceNorm
          (reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • C0N ν Φ F) 1 phi : SymSector ℂ (L2T L) (k + q)) :
                HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • LN ν Φ F b) 1 phi : SymSector ℂ (L2T L) (k + q)) :
                HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal ((C0 * (C1 * M0)) * (∫ θ, w θ * δ θ ∂ν) *
            (Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
              ((|κ| * L) * Real.exp (|κ| * L)))))) := by
  obtain ⟨m, C0, hm, hC0, hmain⟩ := QuantumNLS.MixedCommutator.prop026_traceNorm_transfer d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ L _ κ k q hN Φ F hF b hKQ hbQ hcomm hB hFm hdF phi hphi δ hδ hphiδ
    z h hz hquad w hw0 hw hwδ {M0} hM0 hFb => ?_⟩
  exact hC1b ν L κ k q hN Φ F hF b hKQ hbQ hcomm hB hFm hdF phi hphi δ hδ hphiδ z h hz hquad
    (fun w' _ r _ => kernel_bound κ r w') w hw0 hw hwδ hM0 hFb

end Final


end QuantumNLS.KernelFactorialBound

#print axioms QuantumNLS.KernelFactorialBound.norm_operator_le_hs
#print axioms QuantumNLS.KernelFactorialBound.card_factorial_mul_volume_chain_le
#print axioms QuantumNLS.KernelFactorialBound.factorial_mul_volume_plusOrder_le
#print axioms QuantumNLS.KernelFactorialBound.kernel_hs_le
#print axioms QuantumNLS.KernelFactorialBound.norm_plusKernel_le_fact
#print axioms QuantumNLS.KernelFactorialBound.norm_minusKernel_le_fact
#print axioms QuantumNLS.KernelFactorialBound.norm_physicalKernel_le_fact
#print axioms QuantumNLS.KernelFactorialBound.kernel_bound
#print axioms QuantumNLS.KernelFactorialBound.prop026_traceNorm_transfer_sharp
