import QuantumNLS.ShortTimeGain

/-!
# EXT-003, Route Y stage (ii), part A: free pieces on time slabs and step objects in `L⁴`

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4). Stage (ii) proves the retarded
Duhamel estimate `L^{4/3} → L⁴` with a time gain by the elementary step-function form of the
Christ–Kiselev argument: the interaction-picture curve `w(t) = S_{(α,t]}F` has bounded `4/3`-variation
(DD1's `‖S_K F‖ ≤ C_L ‖1_K F‖_{4/3}`), it is approximated by dyadic step functions adapted to the
`L^{4/3}` mass of `F`, and on each step the free estimate with gain (SG1) applies.

This part builds the `L⁴(J × 𝕋_L)` objects for `t ↦ 1_{(c,d]}(t) U(t)G` ("pieces"), their norms
(`‖piece‖⁴ ≤ K (d−c)^{1/4} ‖G‖⁴`, SG1), their slices, and finite sums over disjoint time slabs.

Imports the frozen SG1 (`ShortTimeGain`, `c06584fb…`), DD1, LS2, LS1 read-only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.ShortTimeGain

namespace QuantumNLS.DuhamelL4

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-- The time slab `(c, d] × 𝕋_L`. -/
def slab (c d : ℝ) : Set (ℝ × AddCircle L) := Set.Ioc c d ×ˢ Set.univ

lemma measurableSet_slab (c d : ℝ) : MeasurableSet (slab (L := L) c d) :=
  measurableSet_Ioc.prod MeasurableSet.univ

lemma μJ_restrict {α β c d : ℝ} (hc : α ≤ c) (hd : d ≤ β) :
    (μJ (L := L) α β).restrict (slab c d) = μJ c d := by
  show ((volume.restrict (Set.Ioc α β)).prod volume).restrict (Set.Ioc c d ×ˢ Set.univ) =
    (volume.restrict (Set.Ioc c d)).prod volume
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left (Set.Ioc_subset_Ioc hc hd)]

/-! ## 1. Cutting an `L⁴` class to a slab -/

/-- `1_E f` as an element of `L⁴`. -/
def ind {α β : ℝ} (c d : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) : Lp ℂ 4 (μJ (L := L) α β) :=
  ((Lp.memLp f).indicator (measurableSet_slab c d)).toLp _

lemma coeFn_ind {α β : ℝ} (c d : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) :
    (ind c d f : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β] (slab c d).indicator f :=
  MemLp.coeFn_toLp _

lemma norm_ind_sub_le {α β : ℝ} (c d : ℝ) (f g : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖ind c d f - ind c d g‖ ≤ ‖f - g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp _).ne ?_
  have h1 : (⇑(ind c d f - ind c d g) : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β]
      (slab c d).indicator (⇑(f - g)) := by
    filter_upwards [Lp.coeFn_sub (ind c d f) (ind c d g), coeFn_ind c d f, coeFn_ind c d g,
      Lp.coeFn_sub f g] with p h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hp : p ∈ slab c d
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp, h4,
        Pi.sub_apply]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp,
        sub_zero]
  rw [eLpNorm_congr_ae h1]
  exact eLpNorm_indicator_le _ (measurableSet_slab c d)

/-! ## 2. Free pieces -/

/-- `t ↦ 1_{(c,d]}(t) U(t)G` as an element of `L⁴(J × 𝕋_L)`. -/
def piece (α β c d : ℝ) (G : HL L) : Lp ℂ 4 (μJ (L := L) α β) := ind c d (freeL4 α β G)

/-- The truncated pieces have the `(c,d]` space-time integral as fourth power of the norm. -/
lemma norm_ind_wN_pow {α β c d : ℝ} (hc : α ≤ c) (hcd : c ≤ d) (hd : d ≤ β) (G : HL L) (N : ℕ) :
    ‖ind c d (wN G α β N)‖ ^ 4 =
      ∫ t in c..d, ∫ x, ‖freeSol (L := L) (win N) (coef G) t x‖ ^ 4 := by
  have hae : (ind c d (wN G α β N) : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β]
      (slab c d).indicator (solP (L := L) (win N) (coef G)) := by
    filter_upwards [coeFn_ind c d (wN G α β N), MemLp.coeFn_toLp (memLp_solP (L := L)
      (win N) (coef G) α β)] with p h1 h2
    rw [h1]
    by_cases hp : p ∈ slab c d
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; exact h2
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  rw [Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_indicator_eq_eLpNorm_restrict
    (measurableSet_slab c d), μJ_restrict hc hd, ← norm_toLp_pow (L := L) _ _ hcd,
    Lp.norm_toLp]

lemma tendsto_ind {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (c d : ℝ) (G : HL L) :
    Tendsto (fun N => ind c d (wN G α β N)) atTop (𝓝 (piece α β c d G)) := by
  have h := tendsto_freeL4 hαβ hlen G
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) h
  exact norm_ind_sub_le c d _ _

/-- **Free pieces with gain**: for `α ≤ c < d ≤ β`, `β − α ≤ T_L`, `d − c ≤ 1`,
`‖1_{(c,d]} U(·)G‖⁴_{L⁴} ≤ K (d−c)^{1/4} ‖G‖⁴`. -/
lemma norm_piece_pow {α β c d : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (hc : α ≤ c)
    (hcd : c < d) (hd : d ≤ β) (h1 : d - c ≤ 1) (G : HL L) :
    ‖piece α β c d G‖ ^ 4 ≤ Kg L * (d - c) ^ (4⁻¹ : ℝ) * ‖G‖ ^ 4 := by
  have hT : 0 < d - c := by linarith
  have hK : 0 ≤ Kg L * (d - c) ^ (4⁻¹ : ℝ) := mul_nonneg Kg_nonneg (Real.rpow_nonneg hT.le _)
  refine le_of_tendsto (((continuous_pow 4).tendsto _).comp
    ((continuous_norm.tendsto _).comp (tendsto_ind hαβ hlen c d G)))
    (Eventually.of_forall fun N => ?_)
  show ‖ind c d (wN G α β N)‖ ^ 4 ≤ _
  rw [norm_ind_wN_pow hc hcd.le hd]
  have hg := gain_finite' (L := L) (win N) (coef G) c hT h1
  rw [show c + (d - c) = d by ring] at hg
  refine hg.trans ?_
  have h0 : 0 ≤ Psum G N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : (∑ n ∈ win N, ‖coef G n‖ ^ 2) ^ 2 ≤ ‖G‖ ^ 4 := by
    have := pow_le_pow_left₀ h0 (Psum_le G N) 2
    rw [← pow_mul] at this
    exact this
  exact mul_le_mul_of_nonneg_left h2 hK

/-- Slices of a piece: for a.e. `t`, `piece(t, ·) = 1_{(c,d]}(t) U(t)G`. -/
lemma piece_slice {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (c d : ℝ) (G : HL L) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), (fun x => piece α β c d G (t, x)) =ᵐ[volume]
      fun x => (Set.Ioc c d).indicator (fun t => (evol G t : AddCircle L → ℂ) x) t := by
  have h1 := Measure.ae_ae_of_ae_prod (coeFn_ind (L := L) c d (freeL4 α β G))
  filter_upwards [h1, freeL4_slice hαβ hlen G] with t ht1 ht2
  filter_upwards [ht1, ht2] with x hx1 hx2
  simp only [piece] at hx1 ⊢
  rw [hx1]
  by_cases ht : t ∈ Set.Ioc c d
  · have hp : (t, x) ∈ slab (L := L) c d := ⟨ht, Set.mem_univ _⟩
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem ht]; exact hx2
  · have hp : (t, x) ∉ slab (L := L) c d := fun h => ht h.1
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem ht]

#print axioms norm_piece_pow
#print axioms piece_slice

/-! ## 3. Fourth powers of norms and disjoint time slabs -/

lemma norm_pow_eq_integral {α β : ℝ} (f : Lp ℂ 4 (μJ (L := L) α β)) :
    ‖f‖ ^ 4 = ∫ p, ‖f p‖ ^ 4 ∂(μJ α β) := by
  have hm := Lp.memLp f
  rw [Lp.norm_def, hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat]
  have hI : 0 ≤ ∫ p, ‖f p‖ ^ (4 : ℝ) ∂(μJ α β) := integral_nonneg fun p => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    show ((4 : ℝ))⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.rpow_inv_natCast_pow hI (by norm_num)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  exact_mod_cast Real.rpow_natCast _ 4

lemma integrable_norm_pow4 {α β : ℝ} (g : Lp ℂ 4 (μJ (L := L) α β)) :
    Integrable (fun p => ‖g p‖ ^ 4) (μJ α β) := by
  have h := (Lp.memLp g).integrable_norm_rpow (by norm_num) (by norm_num)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [ENNReal.toReal_ofNat]
  exact_mod_cast Real.rpow_natCast _ 4

lemma coeFn_finsetSum {α β : ℝ} {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 4 (μJ (L := L) α β)) :
    (⇑(∑ i ∈ s, f i) : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β] fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with p h1 h2
    rw [h1, Pi.add_apply, h2]

/-- **Disjoint time slabs**: `‖Σ_i 1_{(c_i,d_i]} f_i‖⁴ = Σ_i ‖1_{(c_i,d_i]} f_i‖⁴`. -/
lemma norm_sum_ind_pow {α β : ℝ} {ι : Type*} (s : Finset ι) (c d : ι → ℝ)
    (f : ι → Lp ℂ 4 (μJ (L := L) α β))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Set.Ioc (c i) (d i)) (Set.Ioc (c j) (d j))) :
    ‖∑ i ∈ s, ind (c i) (d i) (f i)‖ ^ 4 = ∑ i ∈ s, ‖ind (c i) (d i) (f i)‖ ^ 4 := by
  classical
  have hall : ∀ᵐ p ∂(μJ (L := L) α β), ∀ i ∈ s,
      ind (c i) (d i) (f i) p = (slab (c i) (d i)).indicator (f i) p :=
    (eventually_all_finset s).mpr fun i _ => coeFn_ind (c i) (d i) (f i)
  have hpt : ∀ᵐ p ∂(μJ (L := L) α β), ‖(∑ i ∈ s, ind (c i) (d i) (f i)) p‖ ^ 4 =
      ∑ i ∈ s, ‖ind (c i) (d i) (f i) p‖ ^ 4 := by
    filter_upwards [coeFn_finsetSum s fun i => ind (c i) (d i) (f i), hall] with p h1 h2
    rw [h1, Finset.sum_congr rfl fun i hi => h2 i hi,
      Finset.sum_congr rfl fun i hi => congrArg (fun z => ‖z‖ ^ 4) (h2 i hi)]
    by_cases hex : ∃ i ∈ s, p ∈ slab (L := L) (c i) (d i)
    · obtain ⟨i, hi, hpi⟩ := hex
      have hz : ∀ j ∈ s, j ≠ i → (slab (L := L) (c j) (d j)).indicator (f j) p = 0 := by
        intro j hj hji
        refine Set.indicator_of_notMem (fun hpj => ?_) _
        exact Set.disjoint_left.mp (hdisj i hi j hj (Ne.symm hji)) hpi.1 hpj.1
      have hz' : ∀ j ∈ s, j ≠ i → ‖(slab (L := L) (c j) (d j)).indicator (f j) p‖ ^ 4 = 0 := by
        intro j hj hji
        rw [hz j hj hji, norm_zero]; norm_num
      rw [Finset.sum_eq_single_of_mem i hi hz, Finset.sum_eq_single_of_mem i hi hz']
    · simp only [not_exists, not_and] at hex
      have h0 : ∑ j ∈ s, (slab (L := L) (c j) (d j)).indicator (f j) p = 0 :=
        Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _
      have h0' : ∑ j ∈ s, ‖(slab (L := L) (c j) (d j)).indicator (f j) p‖ ^ 4 = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [Set.indicator_of_notMem (hex j hj) _]; norm_num
      rw [h0, h0']; norm_num
  rw [norm_pow_eq_integral, integral_congr_ae hpt,
    integral_finsetSum _ fun i _ => integrable_norm_pow4 _]
  exact Finset.sum_congr rfl fun i _ => (norm_pow_eq_integral _).symm

#print axioms norm_sum_ind_pow

/-! ## 4. The `L^{4/3}` mass of `F` in time -/

section Mass

variable {α β : ℝ} (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

lemma r43 : (4 / 3 : ℝ≥0∞).toReal = 4 / 3 := by
  rw [ENNReal.toReal_div]; norm_num

/-- `|F|^{4/3}`. -/
def g43 (p : ℝ × AddCircle L) : ℝ := ‖F p‖ ^ (4 / 3 : ℝ)

lemma integrable_g43 : Integrable (g43 F) (μJ α β) := by
  have h := (Lp.memLp F).integrable_norm_rpow (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  rw [r43] at h
  exact h

lemma g43_nonneg (p : ℝ × AddCircle L) : 0 ≤ g43 F p := Real.rpow_nonneg (norm_nonneg _) _

/-- `m(t) = ∫_{(α,t] × 𝕋_L} |F|^{4/3}`. -/
def mass (t : ℝ) : ℝ := ∫ p, (slab α t).indicator (g43 F) p ∂(μJ α β)

/-- `‖1_E F‖_{4/3}^{4/3} = ∫_E |F|^{4/3}`. -/
lemma eLpNorm_ind_pow (c d : ℝ) :
    ((eLpNorm ((slab c d).indicator F) (4 / 3) (μJ α β)).toReal) ^ (4 / 3 : ℝ) =
      ∫ p, (slab c d).indicator (g43 F) p ∂(μJ α β) := by
  have hm : MemLp ((slab (L := L) c d).indicator F) (4 / 3) (μJ α β) :=
    (Lp.memLp F).indicator (measurableSet_slab c d)
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)), r43]
  have hI : 0 ≤ ∫ p, ‖(slab (L := L) c d).indicator F p‖ ^ (4 / 3 : ℝ) ∂(μJ α β) :=
    integral_nonneg fun p => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_mul hI]
  rw [show (4 / 3 : ℝ)⁻¹ * (4 / 3) = 1 by norm_num, Real.rpow_one]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show ‖(slab (L := L) c d).indicator F p‖ ^ (4 / 3 : ℝ) = (slab c d).indicator (g43 F) p
  by_cases hp : p ∈ slab (L := L) c d
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; rfl
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, norm_zero,
      Real.zero_rpow (by norm_num)]

/-- Additivity: `m(d) − m(c) = ∫_{(c,d]} |F|^{4/3}` for `α ≤ c ≤ d`. -/
lemma mass_sub {c d : ℝ} (hc : α ≤ c) (hcd : c ≤ d) :
    mass F d - mass F c = ∫ p, (slab c d).indicator (g43 F) p ∂(μJ α β) := by
  have hU : slab (L := L) α d = slab α c ∪ slab c d := by
    simp only [slab, ← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hc hcd]
  have hD : Disjoint (slab (L := L) α c) (slab c d) :=
    Set.disjoint_prod.mpr (Or.inl (Set.Ioc_disjoint_Ioc_of_le le_rfl))
  unfold mass
  rw [hU, Set.indicator_union_of_disjoint hD, integral_add
    ((integrable_g43 F).indicator (measurableSet_slab _ _))
    ((integrable_g43 F).indicator (measurableSet_slab _ _))]
  ring

lemma mass_mono {c d : ℝ} (hc : α ≤ c) (hcd : c ≤ d) : mass F c ≤ mass F d := by
  have h := mass_sub F hc hcd
  have : 0 ≤ ∫ p, (slab (L := L) c d).indicator (g43 F) p ∂(μJ α β) :=
    integral_nonneg fun p => Set.indicator_nonneg (fun p _ => g43_nonneg F p) p
  linarith

lemma mass_nonneg (t : ℝ) : 0 ≤ mass F t :=
  integral_nonneg fun p => Set.indicator_nonneg (fun p _ => g43_nonneg F p) p

lemma mass_self : mass F α = 0 := by
  unfold mass
  have : slab (L := L) α α = ∅ := by simp [slab]
  rw [this, Set.indicator_empty, integral_zero]

#print axioms mass_sub
#print axioms eLpNorm_ind_pow

end Mass

/-! ## 5. Short intervals carry small mass; increments of `R`; the generalized inverse `τ` -/

section Tau

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

lemma mass_small : ∀ ε > 0, ∃ δ > 0, ∀ c d : ℝ, α ≤ c → c ≤ d → d - c < δ →
    mass F d - mass F c < ε := by
  have hL : 0 < L := Fact.out
  intro ε hε
  set η : ℝ := (ε / 2) ^ (3 / 4 : ℝ)
  have hη : 0 < η := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨δE, hδE, hind⟩ := (Lp.memLp F).eLpNorm_indicator_le (by exact Fact.out)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (ε := ENNReal.ofReal η)
    (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδE
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
  refine ⟨r / L, by positivity, fun c d hc hcd hlt => ?_⟩
  rw [mass_sub F hc hcd, ← eLpNorm_ind_pow]
  have hμ : μJ (L := L) α β (slab c d) ≤ δE := by
    have h1 : slab (L := L) c d ⊆ Set.uIoc c d ×ˢ Set.univ := fun p hp =>
      ⟨Set.Ioc_subset_uIoc hp.1, hp.2⟩
    refine (measure_mono h1).trans ((measure_cut_le (L := L) (α := α) (β := β) c d).trans ?_)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hr2.le
    have := (lt_div_iff₀ hL).mp hlt
    rw [abs_of_nonneg (by linarith)]; linarith
  have hb := hind _ (measurableSet_slab c d) hμ
  have hle : (eLpNorm ((slab (L := L) c d).indicator F) (4 / 3) (μJ α β)).toReal ≤ η := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rwa [ENNReal.toReal_ofReal hη.le] at this
  calc ((eLpNorm ((slab (L := L) c d).indicator F) (4 / 3) (μJ α β)).toReal) ^ (4 / 3 : ℝ)
      ≤ η ^ (4 / 3 : ℝ) := Real.rpow_le_rpow ENNReal.toReal_nonneg hle (by norm_num)
    _ = ε / 2 := by rw [← Real.rpow_mul (by positivity)]; norm_num
    _ < ε := by linarith

include hαβ hlen in
/-- `‖S_{(α,d]}F − S_{(α,c]}F‖ ≤ C_L (m(d) − m(c))^{3/4}`. -/
lemma norm_Rt_sub {c d : ℝ} (hc : α ≤ c) (hcd : c ≤ d) :
    ‖Rt hαβ hlen F d - Rt hαβ hlen F c‖ ≤ CL L * (mass F d - mass F c) ^ (3 / 4 : ℝ) := by
  rw [Rt, Rt, ← rep_sub]
  refine (norm_rep_le _ _ _).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) CL_nonneg)
  have he : Fcut F d - Fcut F c = (slab (L := L) c d).indicator F := by
    funext p
    rw [Pi.sub_apply, Fcut_sub F hc (hc.trans hcd) p]
    have : Set.Ioc d c = ∅ := Set.Ioc_eq_empty (not_lt.mpr hcd)
    simp [this, slab]
  rw [he, mass_sub F hc hcd, ← eLpNorm_ind_pow, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

/-- `τ(λ) = sup {t ∈ [α, β] : m(t) ≤ λ}`. -/
def tau (lam : ℝ) : ℝ := sSup {t ∈ Set.Icc α β | mass F t ≤ lam}

include hαβ in
lemma tau_set_ne {lam : ℝ} (hl : 0 ≤ lam) :
    ({t ∈ Set.Icc α β | mass F t ≤ lam} : Set ℝ).Nonempty :=
  ⟨α, ⟨le_rfl, hαβ⟩, by rw [mass_self]; exact hl⟩

lemma tau_set_bdd (lam : ℝ) : BddAbove ({t ∈ Set.Icc α β | mass F t ≤ lam} : Set ℝ) :=
  ⟨β, fun _ ht => ht.1.2⟩

include hαβ in
lemma tau_mem {lam : ℝ} (hl : 0 ≤ lam) : tau F lam ∈ Set.Icc α β :=
  ⟨le_csSup (tau_set_bdd F lam) ⟨⟨le_rfl, hαβ⟩, by rw [mass_self]; exact hl⟩,
    csSup_le (tau_set_ne hαβ F hl) fun _ ht => ht.1.2⟩

include hαβ in
lemma mass_tau_le {lam : ℝ} (hl : 0 ≤ lam) : mass F (tau F lam) ≤ lam := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨δ, hδ, hsm⟩ := mass_small F (mass F (tau F lam) - lam) (by linarith)
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_lt_csSup (tau_set_ne hαβ F hl)
    (show tau F lam - δ < tau F lam by linarith)
  have ht_le : t ≤ tau F lam := le_csSup (tau_set_bdd F lam) ht
  have := hsm t (tau F lam) ht.1.1 ht_le (by linarith)
  linarith [ht.2]

include hαβ in
lemma mass_tau {lam : ℝ} (hl : 0 ≤ lam) (hlM : lam ≤ mass F β) : mass F (tau F lam) = lam := by
  refine le_antisymm (mass_tau_le hαβ F hl) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hmem := tau_mem hαβ F hl
  rcases eq_or_lt_of_le hmem.2 with heq | hlt
  · rw [heq] at hcon; linarith
  · obtain ⟨δ, hδ, hsm⟩ := mass_small F (lam - mass F (tau F lam)) (by linarith)
    set t := min β (tau F lam + δ / 2)
    have ht1 : tau F lam < t := lt_min hlt (by linarith)
    have ht2 : t ≤ β := min_le_left _ _
    have hm := hsm (tau F lam) t hmem.1 ht1.le (by
      have := min_le_right β (tau F lam + δ / 2); linarith)
    have htS : t ∈ ({t ∈ Set.Icc α β | mass F t ≤ lam} : Set ℝ) :=
      ⟨⟨hmem.1.trans ht1.le, ht2⟩, by linarith⟩
    have : t ≤ tau F lam := le_csSup (tau_set_bdd F lam) htS
    linarith

include hαβ in
lemma tau_mono {l1 l2 : ℝ} (h0 : 0 ≤ l1) (h : l1 ≤ l2) : tau F l1 ≤ tau F l2 :=
  csSup_le_csSup (tau_set_bdd F l2) (tau_set_ne hαβ F h0) fun _ ht => ⟨ht.1, ht.2.trans h⟩

#print axioms norm_Rt_sub
#print axioms mass_tau
#print axioms tau_mono

end Tau

/-! ## 6. Algebra of pieces -/

lemma ind_split {α β c d e : ℝ} (hcd : c ≤ d) (hde : d ≤ e) (f : Lp ℂ 4 (μJ (L := L) α β)) :
    ind c e f = ind c d f + ind d e f := by
  have hU : slab (L := L) c e = slab c d ∪ slab d e := by
    simp only [slab, ← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hcd hde]
  have hD : Disjoint (slab (L := L) c d) (slab d e) :=
    Set.disjoint_prod.mpr (Or.inl (Set.Ioc_disjoint_Ioc_of_le le_rfl))
  refine Lp.ext ?_
  filter_upwards [coeFn_ind c e f, Lp.coeFn_add (ind c d f) (ind d e f), coeFn_ind c d f,
    coeFn_ind d e f] with p h1 h2 h3 h4
  rw [h1, h2, Pi.add_apply, h3, h4, hU, Set.indicator_union_of_disjoint hD]

lemma ind_sub {α β c d : ℝ} (f g : Lp ℂ 4 (μJ (L := L) α β)) :
    ind c d (f - g) = ind c d f - ind c d g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ind c d (f - g), Lp.coeFn_sub (ind c d f) (ind c d g), coeFn_ind c d f,
    coeFn_ind c d g, Lp.coeFn_sub f g] with p h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4]
  by_cases hp : p ∈ slab (L := L) c d
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp, h5,
      Pi.sub_apply]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp,
      sub_zero]

lemma freeL4_sub {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (G₁ G₂ : HL L) :
    freeL4 α β (G₁ - G₂) = freeL4 α β G₁ - freeL4 α β G₂ := by
  rw [sub_eq_add_neg, freeL4_add hαβ hlen, show -G₂ = (-1 : ℂ) • G₂ by simp,
    freeL4_smul hαβ hlen]
  simp [sub_eq_add_neg]

lemma piece_sub {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (c d : ℝ) (G₁ G₂ : HL L) :
    piece α β c d (G₁ - G₂) = piece α β c d G₁ - piece α β c d G₂ := by
  simp only [piece]; rw [freeL4_sub hαβ hlen, ind_sub]

lemma norm_ind_empty {α β : ℝ} (c : ℝ) (f : Lp ℂ 4 (μJ (L := L) α β)) : ‖ind c c f‖ = 0 := by
  have h0 : (ind c c f : ℝ × AddCircle L → ℂ) =ᵐ[μJ α β] 0 := by
    filter_upwards [coeFn_ind c c f] with p hp
    rw [hp]
    have : slab (L := L) c c = ∅ := by simp [slab]
    rw [this, Set.indicator_empty]; rfl
  rw [Lp.norm_def, eLpNorm_congr_ae h0, eLpNorm_zero, ENNReal.toReal_zero]

/-- Pieces with a uniform gain for all `α ≤ c ≤ d ≤ β`, `β − α ≤ min(1, T_L)`. -/
lemma norm_piece_pow_le {α β c d : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1)
    (hc : α ≤ c) (hcd : c ≤ d) (hd : d ≤ β) (G : HL L) :
    ‖piece α β c d G‖ ^ 4 ≤ Kg L * (β - α) ^ (4⁻¹ : ℝ) * ‖G‖ ^ 4 := by
  rcases eq_or_lt_of_le hcd with heq | hlt
  · subst heq
    rw [piece, norm_ind_empty, zero_pow (by norm_num)]
    have := Kg_nonneg (L := L)
    have : 0 ≤ (β - α) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  · refine (norm_piece_pow hαβ hlen hc hlt hd (by linarith) G).trans ?_
    have hK := Kg_nonneg (L := L)
    have hr : (d - c) ^ (4⁻¹ : ℝ) ≤ (β - α) ^ (4⁻¹ : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hG : 0 ≤ ‖G‖ ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hr hK
    exact mul_le_mul_of_nonneg_right this hG

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (h : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), h i = ∑ j ∈ Finset.range m, (h (2 * j) + h (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

#print axioms ind_split
#print axioms norm_piece_pow_le

/-! ## 7. Dyadic step objects adapted to the mass of `F` -/

section Steps

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

/-- The level-`n` mass levels `λ_{n,j} = j M / 2ⁿ`, `M = m(β)`. -/
def lev (n j : ℕ) : ℝ := (j : ℝ) * mass F β / 2 ^ n

/-- The level-`n` partition points `τ_{n,j} = τ(λ_{n,j})`. -/
def tp (n j : ℕ) : ℝ := tau F (lev F n j)

lemma lev_nonneg (n j : ℕ) : 0 ≤ lev F n j := by
  unfold lev; have := mass_nonneg F β; positivity

lemma lev_le (n j : ℕ) (hj : j ≤ 2 ^ n) : lev F n j ≤ mass F β := by
  unfold lev
  have hM := mass_nonneg F β
  rw [div_le_iff₀ (by positivity)]
  have : (j : ℝ) ≤ 2 ^ n := by exact_mod_cast hj
  nlinarith

lemma lev_two_mul (n j : ℕ) : lev F (n + 1) (2 * j) = lev F n j := by
  unfold lev; push_cast; rw [pow_succ]; field_simp

lemma tp_two_mul (n j : ℕ) : tp F (n + 1) (2 * j) = tp F n j := by
  unfold tp; rw [lev_two_mul]

lemma tp_two_mul_add_two (n j : ℕ) : tp F (n + 1) (2 * j + 2) = tp F n (j + 1) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, tp_two_mul]

include hαβ in
lemma tp_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : tp F n j ≤ tp F n k := by
  unfold tp
  refine tau_mono hαβ F (lev_nonneg F n j) ?_
  unfold lev
  have : (j : ℝ) ≤ k := by exact_mod_cast h
  have hM := mass_nonneg F β
  gcongr

include hαβ in
lemma tp_mem (n j : ℕ) : tp F n j ∈ Set.Icc α β := tau_mem hαβ F (lev_nonneg F n j)

include hαβ in
lemma mass_tp (n j : ℕ) (hj : j ≤ 2 ^ n) : mass F (tp F n j) = lev F n j :=
  mass_tau hαβ F (lev_nonneg F n j) (lev_le F n j hj)

/-- The level-`n` step object `O_n = Σ_j 1_{(τ_{n,j}, τ_{n,j+1}]} U(t) R(τ_{n,j})`. -/
def stepObj (n : ℕ) : Lp ℂ 4 (μJ (L := L) α β) :=
  ∑ j ∈ Finset.range (2 ^ n), piece α β (tp F n j) (tp F n (j + 1)) (Rt hαβ hlen F (tp F n j))

/-- **Telescoping identity**: `O_{n+1} − O_n` lives on the odd fine cells. -/
lemma stepObj_succ_sub (n : ℕ) :
    stepObj hαβ hlen F (n + 1) - stepObj hαβ hlen F n =
      ∑ j ∈ Finset.range (2 ^ n), piece α β (tp F (n + 1) (2 * j + 1)) (tp F (n + 1) (2 * j + 2))
        (Rt hαβ hlen F (tp F (n + 1) (2 * j + 1)) - Rt hαβ hlen F (tp F (n + 1) (2 * j))) := by
  unfold stepObj
  rw [pow_succ, mul_comm, sum_range_two_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : tp F (n + 1) (2 * j) ≤ tp F (n + 1) (2 * j + 1) := tp_mono hαβ F _ (by omega)
  have h2 : tp F (n + 1) (2 * j + 1) ≤ tp F (n + 1) (2 * j + 2) := tp_mono hαβ F _ (by omega)
  rw [show 2 * j + 1 + 1 = 2 * j + 2 by ring]
  have e1 := tp_two_mul F n j
  have e2 := tp_two_mul_add_two F n j
  rw [← e1, ← e2]
  simp only [piece]
  rw [ind_split h1 h2, freeL4_sub hαβ hlen, ind_sub]
  abel

#print axioms stepObj_succ_sub

end Steps

end QuantumNLS.DuhamelL4
