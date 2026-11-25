import QuantumNLS.L4Uniqueness
import QuantumNLS.F04Global
import QuantumNLS.DuhamelDualityLocal

/-!
# EXT-003, Route Y stage (v), part B: the `H¹` flow as an `L⁴` Duhamel solution; mass conservation

Toward R-AEE17FD6 (`thm:root-L2-flow`): "Approximate `f` in `L²` by smooth periodic `f_j`, with all
norms bounded by a common radius. Their global `H¹` solutions from Theorem `F04:thm-global` belong
to the local `L⁴` uniqueness class, so agree there with the solutions just constructed. The local
Lipschitz bounds ... give convergence ... Conservation for the regular solutions and convergence in
`C_tL²_x` yield `‖u(t)‖₂ = ‖f‖₂` throughout the local interval."

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4); linear inputs LS1/LS2, DD1,
DDL1, SG1, DL4a/DL4b, LC1, UQ1 (read-only); the `H¹` flow is GL1 (`F04Global.thm_global`,
read-only).

Here:
* `emb : h¹ → L²(𝕋_L)` (the continuous representative `Σ a_n e_n`), with `emb ∘ S(t) = U(t) ∘ emb`
  and `emb (F(a)) = |emb a|² emb a`;
* **`bridge`**: for `κ ≥ 0`, `g ∈ h¹` and any data time `a ∈ [α, β]`, the `H¹` solution
  `t ↦ u(t − a)` (GL1, data `g`) defines an `L⁴(J × 𝕋_L)` solution of the cubic Duhamel equation
  `u(t) = U(t−a) g − 2iκ ∫_a^t U(t−s)(|u|²u)(s) ds` on `J = (α, β]`, whose continuous `L²` curve is
  `emb (u(t − a))` for every `t ∈ [α, β]`;
* **`mass_local`**: for `κ ≥ 0` and every `R ≥ 0` there is `τ > 0` such that every `L⁴` Duhamel
  solution on an interval of length `≤ τ` with data `‖f‖₂ ≤ R` (at any data time `a ∈ J`) has
  `‖u(t)‖₂ = ‖f‖₂` for every `t ∈ [α, β]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.DuhamelL4Limit
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Uniqueness
open QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull
  QuantumNLS.F04Regularity QuantumNLS.Sobolev.PosWeight

namespace QuantumNLS.H1Bridge

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. The embedding `h¹ → L²` -/

/-- `a ↦ Σ a_n e_n` as an element of `L²(𝕋_L)`. -/
def emb : h04 L 1 →L[ℂ] HL L :=
  (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ).comp S1

lemma emb_coeFn (a : h04 L 1) : (emb a : AddCircle L → ℂ) =ᵐ[volume] (S1 a : AddCircle L → ℂ) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (S1 a)

lemma fourierL2_emb (a : h04 L 1) (n : ℤ) : fourierL2 L (emb a) n = a.val n := by
  rw [fourierL2_apply, coeff_congr_ae L (emb_coeFn a) n, coeff_S1]

lemma emb_Sgrp (a : h04 L 1) (t : ℝ) : emb (Sgrp 1 t a) = evol (emb a) t := by
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  rw [fourierL2_emb, Sgrp_val, fourierL2_evol]
  show _ = _ * fourierL2 L (emb a) n
  rw [fourierL2_emb]

lemma continuous_nlRep (a : h04 L 1) : Continuous (nlRep L a.val) := by
  have h : nlRep L a.val = fun x => ((‖S1 a x‖ ^ 2 : ℝ) : ℂ) * S1 a x := rfl
  rw [h]
  have hc := (S1 a).continuous
  fun_prop

lemma emb_Fh (a : h04 L 1) :
    (emb (Fh (le_refl (1 : ℝ)) a) : AddCircle L → ℂ) =ᵐ[volume] nlRep L a.val := by
  set Nc : C(AddCircle L, ℂ) := ⟨nlRep L a.val, continuous_nlRep a⟩
  have e : emb (Fh (le_refl (1 : ℝ)) a) =
      ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ Nc := by
    apply (fourierL2 L).injective
    refine lp.ext (funext fun n => ?_)
    rw [fourierL2_emb, fourierL2_apply,
      coeff_congr_ae L (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume Nc) n]
    rfl
  rw [e]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume Nc

lemma norm_emb_sq (a : h04 L 1) : ‖emb a‖ ^ 2 = ∫ x, ‖S1 a x‖ ^ 2 := by
  have h1 : ‖emb a‖ ^ 2 = RCLike.re ⟪emb a, emb a⟫_ℂ := (norm_sq_eq_re_inner (𝕜 := ℂ) _)
  rw [h1, MeasureTheory.L2.inner_def]
  have h2 : (fun x => ⟪(emb a : AddCircle L → ℂ) x, (emb a : AddCircle L → ℂ) x⟫_ℂ) =ᵐ[volume]
      fun x => ((‖S1 a x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [emb_coeFn a] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [integral_congr_ae h2, integral_complex_ofReal]
  rfl

/-! ## 2. The space-time function of a continuous `h¹` curve -/

section Joint

variable {α β : ℝ}

/-- `(t, x) ↦ (Σ_n v(t)_n e_n)(x)`. -/
def Φ (v : ℝ → h04 L 1) (p : ℝ × AddCircle L) : ℂ := S1 (v p.1) p.2

lemma continuous_Φ {v : ℝ → h04 L 1} (hv : Continuous v) : Continuous (Φ v) :=
  continuous_eval.comp
    (((S1 (L := L)).continuous.comp (hv.comp continuous_fst)).prodMk continuous_snd)

lemma ae_mem_J : ∀ᵐ p ∂(μJ (L := L) α β), p.1 ∈ Set.Ioc α β := by
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := volume.restrict (Set.Ioc α β))
    (ν := (volume : Measure (AddCircle L))) (measurableSet_Ioc.prod MeasurableSet.univ)).2 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Eventually.of_forall fun _ => ⟨ht, trivial⟩)
  exact h.mono fun p hp => hp.1

lemma memLp_Φ {v : ℝ → h04 L 1} (hv : Continuous v) : MemLp (Φ v) 4 (μJ (L := L) α β) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn hv.continuousOn
  refine MemLp.of_bound (continuous_Φ hv).aestronglyMeasurable (‖(S1 (L := L))‖ * M) ?_
  filter_upwards [ae_mem_J] with p hp
  calc ‖Φ v p‖ = ‖S1 (v p.1) p.2‖ := rfl
    _ ≤ ‖S1 (v p.1)‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖(S1 (L := L))‖ * ‖v p.1‖ := (S1 (L := L)).le_opNorm _
    _ ≤ ‖(S1 (L := L))‖ * M :=
        mul_le_mul_of_nonneg_left (hM _ (Set.Ioc_subset_Icc_self hp)) (norm_nonneg _)

/-- The `L⁴(J × 𝕋_L)` class of a continuous `h¹` curve. -/
def Uv {v : ℝ → h04 L 1} (hv : Continuous v) : Lp ℂ 4 (μJ (L := L) α β) :=
  (memLp_Φ (α := α) (β := β) hv).toLp _

lemma coeFn_Uv {v : ℝ → h04 L 1} (hv : Continuous v) :
    (Uv (α := α) (β := β) hv : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) α β] Φ v :=
  (memLp_Φ (α := α) (β := β) hv).coeFn_toLp

lemma Uv_slice {v : ℝ → h04 L 1} (hv : Continuous v) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => Uv (α := α) (β := β) hv (t, x)) =ᵐ[volume] (emb (v t) : AddCircle L → ℂ) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (coeFn_Uv (α := α) (β := β) hv)] with t ht
  filter_upwards [ht, emb_coeFn (v t)] with x h1 h2
  rw [h1, h2]; rfl

lemma cubUv_slice {v : ℝ → h04 L 1} (hv : Continuous v) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => cub (Uv (α := α) (β := β) hv) (t, x)) =ᵐ[volume]
        (emb (Fh (le_refl (1 : ℝ)) (v t)) : AddCircle L → ℂ) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (coeFn_cub (Uv (α := α) (β := β) hv)),
    Measure.ae_ae_of_ae_prod (coeFn_Uv (α := α) (β := β) hv)] with t h1 h2
  filter_upwards [h1, h2, emb_Fh (v t)] with x x1 x2 x3
  rw [x1, x3]
  show ((‖Uv (α := α) (β := β) hv (t, x)‖ ^ 2 : ℝ) : ℂ) * Uv (α := α) (β := β) hv (t, x) = _
  rw [x2]
  rfl

end Joint

/-! ## 3. The bridge -/

/-- The `H¹` flow (GL1) with data `g` at time `a`: `t ↦ u(t − a)`. -/
def flowAt (κ : ℝ) (g : h04 L 1) (a t : ℝ) : h04 L 1 :=
  umax (le_refl (1 : ℝ)) κ g (t - a)

lemma continuous_flowAt {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a : ℝ) :
    Continuous (flowAt κ g a) :=
  (QuantumNLS.F04Global.thm_global (L := L) hκ g).2.1.comp (continuous_id.sub continuous_const)

/-- The `H¹` Duhamel formula based at the data time `a`. -/
lemma flowAt_duhamel {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a t : ℝ) :
    flowAt κ g a t = Sgrp 1 (t - a) g - (2 * Complex.I * κ) •
      ∫ r in a..t, Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (flowAt κ g a r)) := by
  have hu := (QuantumNLS.F04Global.thm_global (L := L) hκ g).1
  have e := hu.duhamel_eq (t - a) (Set.mem_univ _)
  unfold flowAt
  rw [e]
  unfold duhamel
  congr 2
  have hsub := intervalIntegral.integral_comp_sub_right
    (fun r => Sgrp 1 (t - a - r) (Fh (le_refl (1 : ℝ)) (umax (le_refl (1 : ℝ)) κ g r))) a
    (a := a) (b := t)
  rw [sub_self] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [show t - a - (r - a) = t - r by ring]

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L)

/-- **A continuous `h¹` curve satisfying the `H¹` Duhamel formula from a base time `a` is an `L⁴`
Duhamel solution** on `J ∋ a` (bridge GL1 → EXT-003 class), with continuous `L²` curve `emb ∘ v`. -/
theorem bridge_gen {κ : ℝ} {v : ℝ → h04 L 1} (hv : Continuous v) (a : ℝ)
    (hduh : ∀ t, v t = Sgrp 1 (t - a) (v a) - (2 * Complex.I * κ) •
      ∫ r in a..t, Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (v r)))
    (ha : a ∈ Set.Icc α β) :
    ∃ U : Lp ℂ 4 (μJ (L := L) α β),
      IsDuhamel hαβ hlen (cNLS κ) a (emb (v a)) U ∧
      (∀ t ∈ Set.Icc α β, Dcurve hαβ hlen (cNLS κ) a (emb (v a)) U t = emb (v t)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
        (fun x => U (t, x)) =ᵐ[volume] (emb (v t) : AddCircle L → ℂ) := by
  set U := Uv (α := α) (β := β) hv
  have hF : Continuous fun s => Fh (le_refl (1 : ℝ)) (v s) := (continuous_Fh _).comp hv
  have key : ∀ t ∈ Set.Icc α β,
      Dcurve hαβ hlen (cNLS κ) a (emb (v a)) U t = emb (v t) := by
    intro t ht
    have hsub : Set.uIoc a t ⊆ Set.Ioc α β :=
      Set.Ioc_subset_Ioc (le_min ha.1 ht.1) (max_le ha.2 ht.2)
    have hFc : Continuous fun s => emb (Fh (le_refl (1 : ℝ)) (v s)) := emb.continuous.comp hF
    have hV := QuantumNLS.DuhamelDualityLocal.V_eq_integral_local hαβ hlen (cub U)
      (fun s => emb (Fh (le_refl (1 : ℝ)) (v s)))
      ((hFc.continuousOn.integrableOn_compact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
      (ae_restrict_of_ae_restrict_of_subset hsub (cubUv_slice hv)) ha ht
    have hint : IntervalIntegrable (fun r => Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (v r)))
        volume a t :=
      (continuousOn_Sgrp (continuous_const.sub continuous_id) hF.continuousOn).intervalIntegrable
    have hcomm := emb.intervalIntegral_comp_comm hint
    have hdu := hduh t
    rw [Dcurve, hV, ← emb_Sgrp]
    simp_rw [← emb_Sgrp]
    rw [hcomm, hdu, map_sub, map_smul, cNLS,
      show -(2 * (κ : ℂ) * Complex.I) = -(2 * Complex.I * κ) by ring, neg_smul, ← sub_eq_add_neg]
  refine ⟨U, ?_, key, Uv_slice hv⟩
  filter_upwards [Uv_slice hv, ae_restrict_mem measurableSet_Ioc] with t h1 h2
  have e := key t (Set.Ioc_subset_Icc_self h2)
  rw [Dcurve] at e
  rw [e]
  exact h1

lemma flowAt_self {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a : ℝ) : flowAt κ g a a = g := by
  unfold flowAt
  rw [sub_self]
  exact (QuantumNLS.F04Global.thm_global (L := L) hκ g).1.at_zero

/-- **The `H¹` flow with data `g` at time `a` is an `L⁴` Duhamel solution.** -/
theorem bridge {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a : ℝ) (ha : a ∈ Set.Icc α β) :
    ∃ U : Lp ℂ 4 (μJ (L := L) α β),
      IsDuhamel hαβ hlen (cNLS κ) a (emb g) U ∧
      (∀ t ∈ Set.Icc α β, Dcurve hαβ hlen (cNLS κ) a (emb g) U t = emb (flowAt κ g a t)) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
        (fun x => U (t, x)) =ᵐ[volume] (emb (flowAt κ g a t) : AddCircle L → ℂ) := by
  have h := bridge_gen hαβ hlen (continuous_flowAt hκ g a) a (fun t => by
    rw [flowAt_self hκ]; exact flowAt_duhamel hκ g a t) ha
  rwa [flowAt_self hκ] at h

/-- The global `H¹` solution (GL1) satisfies its Duhamel formula from every base time. -/
lemma umax_duhamel {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a t : ℝ) :
    umax (le_refl (1 : ℝ)) κ g t = Sgrp 1 (t - a) (umax (le_refl (1 : ℝ)) κ g a) -
      (2 * Complex.I * κ) • ∫ r in a..t, Sgrp 1 (t - r)
        (Fh (le_refl (1 : ℝ)) (umax (le_refl (1 : ℝ)) κ g r)) :=
  duhamel_rebase (le_refl (1 : ℝ)) (QuantumNLS.F04Global.thm_global (L := L) hκ g).1
    (Set.mem_univ a) (Set.mem_univ t)

/-- Mass conservation of the `H¹` flow, in `L²` form. -/
lemma norm_emb_flowAt {κ : ℝ} (hκ : 0 ≤ κ) (g : h04 L 1) (a t : ℝ) :
    ‖emb (flowAt κ g a t)‖ = ‖emb g‖ := by
  have h := (QuantumNLS.F04Global.thm_global (L := L) hκ g).2.2.2.2.2.2.2.1 (t - a)
  have e : ‖emb (flowAt κ g a t)‖ ^ 2 = ‖emb g‖ ^ 2 := by
    rw [norm_emb_sq, norm_emb_sq, flowAt, h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e

#print axioms bridge_gen
#print axioms bridge
#print axioms norm_emb_flowAt

/-! ## 4. Smooth approximation of `L²` data -/

/-- Fourier truncation `Σ_{|n| ≤ N} f̂(n) e_n` as an element of `h¹`. -/
def trunc (f : HL L) (N : ℕ) : h04 L 1 :=
  WSeq.mk _ (fun n => if n ∈ win N then coef f n else 0) (by
    refine summable_of_ne_finset_zero (s := win N) fun n hn => ?_
    simp [hn])

lemma evol_zero_time (f : HL L) : evol f 0 = f := by
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  rw [fourierL2_evol, phase_zero, one_mul]

lemma emb_trunc (f : HL L) (N : ℕ) :
    emb (trunc f N) = (memLp2_slice (win N) (coef f) 0).toLp
      (fun x => freeSol (L := L) (win N) (coef f) 0 x) := by
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  rw [fourierL2_emb, QuantumNLS.Sobolev.fourierL2_toLp, coeff_freeSol, phase_zero, one_mul]
  rfl

lemma tendsto_trunc (f : HL L) : Tendsto (fun N => emb (trunc f N)) atTop (𝓝 f) := by
  have h := tendsto_slice f 0
  rw [evol_zero_time] at h
  exact h.congr fun N => (emb_trunc f N).symm

lemma norm_trunc_le (f : HL L) (N : ℕ) : ‖emb (trunc f N)‖ ≤ ‖f‖ := by
  have e1 : ‖emb (trunc f N)‖ ^ 2 =
      ∑' n, ‖(if n ∈ win N then coef f n else 0 : ℂ)‖ ^ 2 := by
    rw [← (fourierL2 L).norm_map, norm_sq_lp]
    refine tsum_congr fun n => ?_
    rw [fourierL2_emb]; rfl
  have e2 : ‖f‖ ^ 2 = ∑' n, ‖coef f n‖ ^ 2 := by
    rw [← (fourierL2 L).norm_map, norm_sq_lp]
  have hle : ∀ n, ‖(if n ∈ win N then coef f n else 0 : ℂ)‖ ^ 2 ≤ ‖coef f n‖ ^ 2 := fun n => by
    split_ifs <;> simp
  have hs := summable_coef f
  have hs1 : Summable fun n => ‖(if n ∈ win N then coef f n else 0 : ℂ)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle hs
  have h : ‖emb (trunc f N)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [e1, e2]; exact Summable.tsum_le_tsum hle hs1 hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-! ## 5. Local existence, uniqueness and mass conservation -/

/-- **Local flow with mass conservation** (`κ ≥ 0`): for every `R ≥ 0` there is
`τ ∈ (0, min(1, T_L)]` such that on every `J = (α, β]` with `0 < β − α ≤ τ` and every data time
`a ∈ [α, β]`: every `‖f‖₂ ≤ R` has an `L⁴(J × 𝕋_L)` Duhamel solution, and every such solution
(no norm bound) has `‖u(t)‖₂ = ‖f‖₂` for every `t ∈ [α, β]` (its continuous `L²` curve). -/
theorem local_flow {κ : ℝ} (hκ : 0 ≤ κ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ τ ≤ TL L ∧
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), α < β → β ≤ α + τ →
        ∀ a ∈ Set.Icc α β, ∀ f : HL L, ‖f‖ ≤ R →
          (∃ U : Lp ℂ 4 (μJ (L := L) α β), IsDuhamel hαβ hlen (cNLS κ) a f U) ∧
          ∀ U : Lp ℂ 4 (μJ (L := L) α β), IsDuhamel hαβ hlen (cNLS κ) a f U →
            ∀ t ∈ Set.Icc α β, ‖Dcurve hαβ hlen (cNLS κ) a f U t‖ = ‖f‖ := by
  obtain ⟨τ, B, A, hτ, hτ1, hτL, hB, hA, H⟩ := ext003_local_input (L := L) κ R hR
  refine ⟨τ, hτ, hτ1, hτL, fun α β hαβ hlen hlt hβ a ha f hf => ?_⟩
  obtain ⟨c1, -, -, c4, -⟩ := H α β hαβ hlen hlt hβ a
  have h1 : β - α ≤ 1 := by linarith
  refine ⟨let ⟨u, _, hu⟩ := c1 f hf; ⟨u, hu⟩, fun U hU t ht => ?_⟩
  obtain ⟨u, hub, hu⟩ := c1 f hf
  have hUu : U = u := duhamel_unique hαβ hlen h1 hlt _ a ha f hU hu
  subst hUu
  set D := Dcurve hαβ hlen (cNLS κ) a f U t
  have hbound : ∀ N : ℕ, |‖D‖ - ‖emb (trunc f N)‖| ≤
      (1 + 6 * |κ| * CL L * B ^ 2 * A) * ‖f - emb (trunc f N)‖ := by
    intro N
    have hgN : ‖emb (trunc f N)‖ ≤ R := (norm_trunc_le f N).trans hf
    obtain ⟨UN, hUN, hDN, -⟩ := bridge hαβ hlen hκ (trunc f N) a ha
    obtain ⟨uN, hubN, huN⟩ := c1 _ hgN
    have hUNu : UN = uN := duhamel_unique hαβ hlen h1 hlt _ a ha _ hUN huN
    subst hUNu
    have hc := c4 f (emb (trunc f N)) U UN hf hgN hub hubN hu huN t
    rw [hDN t ht] at hc
    calc |‖D‖ - ‖emb (trunc f N)‖| ≤ ‖D - emb (flowAt κ (trunc f N) a t)‖ := by
          rw [← norm_emb_flowAt hκ (trunc f N) a t]; exact abs_norm_sub_norm_le _ _
      _ ≤ _ := hc
  have hlim : Tendsto (fun N => ‖emb (trunc f N)‖) atTop (𝓝 ‖D‖) := by
    have h0 : Tendsto (fun N => (1 + 6 * |κ| * CL L * B ^ 2 * A) * ‖f - emb (trunc f N)‖) atTop
        (𝓝 0) := by
      have := ((tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_trunc f)).const_mul
        (1 + 6 * |κ| * CL L * B ^ 2 * A))
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      rw [← norm_neg, neg_sub]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) h0
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hbound N
  have hlim2 : Tendsto (fun N => ‖emb (trunc f N)‖) atTop (𝓝 ‖f‖) :=
    (continuous_norm.tendsto f).comp (tendsto_trunc f)
  exact tendsto_nhds_unique hlim hlim2

#print axioms local_flow

end QuantumNLS.H1Bridge
