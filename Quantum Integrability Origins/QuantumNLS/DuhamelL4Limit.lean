import QuantumNLS.DuhamelL4

/-!
# EXT-003, Route Y stage (ii), part B: the dyadic series and its `L⁴` limit

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4): the retarded Duhamel estimate
`L^{4/3} → L⁴` is obtained by the step-function form of the Christ–Kiselev argument.

Imports the frozen stage-(ii) part A (`DuhamelL4`) read-only. Here: the differences of consecutive
dyadic step objects satisfy `‖O_{n+1} − O_n‖⁴ ≤ A (1/4)ⁿ` with
`A = K (β−α)^{1/4} C_L⁴ M³ / 8` (`M` the `L^{4/3}`-mass of `F`), the step objects converge in
`L⁴(J × 𝕋_L)`, and the limit `W` satisfies `‖W‖⁴ ≤ 32 K C_L⁴ (β−α)^{1/4} ‖F‖_{4/3}⁴`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.ShortTimeGain QuantumNLS.DuhamelL4

namespace QuantumNLS.DuhamelL4Limit

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

section Limit

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1)
  (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

/-- `A = K (β−α)^{1/4} C_L⁴ M³ / 8`. -/
def Aq : ℝ := Kg L * (β - α) ^ (4⁻¹ : ℝ) * CL L ^ 4 * mass F β ^ 3 / 8

lemma Aq_nonneg (hαβ : α ≤ β) : 0 ≤ Aq F := by
  unfold Aq
  have := Kg_nonneg (L := L)
  have := CL_nonneg (L := L)
  have := mass_nonneg F β
  have : 0 ≤ (β - α) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by linarith) _
  positivity

lemma rpow_34_pow4 {x : ℝ} (hx : 0 ≤ x) : (x ^ (3 / 4 : ℝ)) ^ 4 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

include hαβ hlen h1 in
/-- `‖O_{n+1} − O_n‖⁴ ≤ A (1/2ⁿ)²`. -/
lemma norm_diff_pow (n : ℕ) :
    ‖stepObj hαβ hlen F (n + 1) - stepObj hαβ hlen F n‖ ^ 4 ≤ Aq F * ((1 / 2 : ℝ) ^ n) ^ 2 := by
  have hdisj : ∀ i ∈ Finset.range (2 ^ n), ∀ j ∈ Finset.range (2 ^ n), i ≠ j →
      Disjoint (Set.Ioc (tp F (n + 1) (2 * i + 1)) (tp F (n + 1) (2 * i + 2)))
        (Set.Ioc (tp F (n + 1) (2 * j + 1)) (tp F (n + 1) (2 * j + 2))) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.Ioc_disjoint_Ioc_of_le (tp_mono hαβ F _ (by omega))
    · exact (Set.Ioc_disjoint_Ioc_of_le (tp_mono hαβ F _ (by omega))).symm
  rw [stepObj_succ_sub]
  simp only [piece]
  rw [norm_sum_ind_pow _ _ _ _ hdisj]
  set M := mass F β
  have hM : 0 ≤ M := mass_nonneg F β
  have hG : ∀ j ∈ Finset.range (2 ^ n),
      ‖Rt hαβ hlen F (tp F (n + 1) (2 * j + 1)) - Rt hαβ hlen F (tp F (n + 1) (2 * j))‖ ^ 4 ≤
        CL L ^ 4 * (M / 2 ^ (n + 1)) ^ 3 := by
    intro j hj
    have hj' : j < 2 ^ n := Finset.mem_range.mp hj
    have hc : α ≤ tp F (n + 1) (2 * j) := (tp_mem hαβ F _ _).1
    have hcd : tp F (n + 1) (2 * j) ≤ tp F (n + 1) (2 * j + 1) := tp_mono hαβ F _ (by omega)
    have hb := norm_Rt_sub hαβ hlen F hc hcd
    have hpow : 2 * j + 1 ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
    rw [mass_tp hαβ F _ _ hpow, mass_tp hαβ F _ _ (by omega)] at hb
    have hlev : lev F (n + 1) (2 * j + 1) - lev F (n + 1) (2 * j) = M / 2 ^ (n + 1) := by
      unfold lev; push_cast; ring
    rw [hlev] at hb
    have h0 : 0 ≤ M / 2 ^ (n + 1) := by positivity
    calc ‖Rt hαβ hlen F (tp F (n + 1) (2 * j + 1)) - Rt hαβ hlen F (tp F (n + 1) (2 * j))‖ ^ 4
        ≤ (CL L * (M / 2 ^ (n + 1)) ^ (3 / 4 : ℝ)) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 4
      _ = CL L ^ 4 * (M / 2 ^ (n + 1)) ^ 3 := by rw [mul_pow, rpow_34_pow4 h0]
  have hK : 0 ≤ Kg L * (β - α) ^ (4⁻¹ : ℝ) :=
    mul_nonneg Kg_nonneg (Real.rpow_nonneg (by linarith) _)
  calc ∑ j ∈ Finset.range (2 ^ n), ‖ind (tp F (n + 1) (2 * j + 1)) (tp F (n + 1) (2 * j + 2))
        (freeL4 α β (Rt hαβ hlen F (tp F (n + 1) (2 * j + 1)) -
          Rt hαβ hlen F (tp F (n + 1) (2 * j))))‖ ^ 4
      ≤ ∑ j ∈ Finset.range (2 ^ n), Kg L * (β - α) ^ (4⁻¹ : ℝ) *
          (CL L ^ 4 * (M / 2 ^ (n + 1)) ^ 3) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hp := norm_piece_pow_le hαβ hlen h1 (tp_mem hαβ F (n + 1) (2 * j + 1)).1
          (tp_mono hαβ F (n + 1) (show 2 * j + 1 ≤ 2 * j + 2 by omega))
          (tp_mem hαβ F (n + 1) (2 * j + 2)).2
          (Rt hαβ hlen F (tp F (n + 1) (2 * j + 1)) - Rt hαβ hlen F (tp F (n + 1) (2 * j)))
        exact hp.trans (mul_le_mul_of_nonneg_left (hG j hj) hK)
    _ = Aq F * ((1 / 2 : ℝ) ^ n) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Aq, one_div_pow, pow_succ]
        push_cast
        field_simp
        ring

#print axioms norm_diff_pow

include hαβ hlen h1 in
lemma dist_step_le (n : ℕ) :
    dist (stepObj hαβ hlen F n) (stepObj hαβ hlen F (n + 1)) ≤
      Aq F ^ (4⁻¹ : ℝ) * (3 / 4 : ℝ) ^ n := by
  rw [dist_comm, dist_eq_norm]
  have hA := Aq_nonneg F hαβ
  have hb : 0 ≤ Aq F ^ (4⁻¹ : ℝ) * (3 / 4 : ℝ) ^ n :=
    mul_nonneg (Real.rpow_nonneg hA _) (by positivity)
  refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hb ?_
  refine (norm_diff_pow hαβ hlen h1 F n).trans ?_
  rw [mul_pow, show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.rpow_inv_natCast_pow hA
    (by norm_num)]
  refine mul_le_mul_of_nonneg_left ?_ hA
  calc ((1 / 2 : ℝ) ^ n) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ ((3 / 4 : ℝ) ^ 4) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    _ = ((3 / 4 : ℝ) ^ n) ^ 4 := by rw [← pow_mul, ← pow_mul, mul_comm]

include hαβ hlen h1 in
lemma cauchy_step : CauchySeq (stepObj hαβ hlen F) :=
  cauchySeq_of_le_geometric (3 / 4) (Aq F ^ (4⁻¹ : ℝ)) (by norm_num) (dist_step_le hαβ hlen h1 F)

/-- The `L⁴` limit `W = lim O_n`. -/
def Wlim : Lp ℂ 4 (μJ (L := L) α β) := limUnder atTop (stepObj hαβ hlen F)

include h1 in
lemma tendsto_Wlim : Tendsto (stepObj hαβ hlen F) atTop (𝓝 (Wlim hαβ hlen F)) := by
  obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete (cauchy_step hαβ hlen h1 F)
  exact tendsto_nhds_limUnder ⟨W, hW⟩

lemma norm_Rt_alpha : ‖Rt hαβ hlen F α‖ = 0 := by
  refine le_antisymm ((norm_rep_le hαβ hlen _).trans (le_of_eq ?_)) (norm_nonneg _)
  have : Fcut F α = 0 := by
    funext p; simp [Fcut]
  rw [this, eLpNorm_zero, ENNReal.toReal_zero, mul_zero]

lemma lev_zero_zero : lev F 0 0 = 0 := by simp [lev]

lemma norm_Rt_tp00 : ‖Rt hαβ hlen F (tp F 0 0)‖ = 0 := by
  have hm : mass F (tp F 0 0) = 0 := by
    rw [mass_tp hαβ F 0 0 (by norm_num), lev_zero_zero]
  have hc : α ≤ tp F 0 0 := (tp_mem hαβ F 0 0).1
  have hb := norm_Rt_sub hαβ hlen F (le_refl α) hc
  rw [hm, mass_self, sub_zero, Real.zero_rpow (by norm_num), mul_zero] at hb
  have h2 : ‖Rt hαβ hlen F (tp F 0 0)‖ ≤
      ‖Rt hαβ hlen F (tp F 0 0) - Rt hαβ hlen F α‖ + ‖Rt hαβ hlen F α‖ := by
    calc ‖Rt hαβ hlen F (tp F 0 0)‖
        = ‖(Rt hαβ hlen F (tp F 0 0) - Rt hαβ hlen F α) + Rt hαβ hlen F α‖ := by abel_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_Rt_alpha] at h2
  exact le_antisymm (by linarith) (norm_nonneg _)

include h1 in
lemma norm_step_zero : ‖stepObj hαβ hlen F 0‖ = 0 := by
  unfold stepObj
  rw [pow_zero, Finset.sum_range_one]
  have hp := norm_piece_pow_le hαβ hlen h1 (tp_mem hαβ F 0 0).1
    (tp_mono hαβ F 0 (show 0 ≤ 0 + 1 by omega)) (tp_mem hαβ F 0 (0 + 1)).2
    (Rt hαβ hlen F (tp F 0 0))
  rw [norm_Rt_tp00, zero_pow (by norm_num), mul_zero] at hp
  have h0 := norm_nonneg (piece α β (tp F 0 0) (tp F 0 (0 + 1)) (Rt hαβ hlen F (tp F 0 0)))
  have : ‖piece α β (tp F 0 0) (tp F 0 (0 + 1)) (Rt hαβ hlen F (tp F 0 0))‖ ^ 4 = 0 :=
    le_antisymm hp (by positivity)
  exact pow_eq_zero_iff (by norm_num) |>.mp this

include h1 in
lemma norm_Wlim_le : ‖Wlim hαβ hlen F‖ ≤ 4 * Aq F ^ (4⁻¹ : ℝ) := by
  have hd := dist_le_of_le_geometric_of_tendsto₀ (3 / 4) (Aq F ^ (4⁻¹ : ℝ)) (by norm_num)
    (dist_step_le hαβ hlen h1 F) (tendsto_Wlim hαβ hlen h1 F)
  rw [dist_eq_norm] at hd
  have h0 := norm_step_zero hαβ hlen h1 F
  calc ‖Wlim hαβ hlen F‖
      = ‖stepObj hαβ hlen F 0 - (stepObj hαβ hlen F 0 - Wlim hαβ hlen F)‖ := by abel_nf
    _ ≤ ‖stepObj hαβ hlen F 0‖ + ‖stepObj hαβ hlen F 0 - Wlim hαβ hlen F‖ := norm_sub_le _ _
    _ ≤ 0 + Aq F ^ (4⁻¹ : ℝ) / (1 - 3 / 4) := by rw [h0]; linarith
    _ = 4 * Aq F ^ (4⁻¹ : ℝ) := by ring

include hαβ in
lemma mass_le_norm : mass F β ≤ ‖F‖ ^ (4 / 3 : ℝ) := by
  have h := mass_sub F (le_refl α) hαβ
  rw [mass_self, sub_zero, ← eLpNorm_ind_pow] at h
  rw [h, Lp.norm_def]
  refine Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (Lp.memLp F).ne (eLpNorm_indicator_le _ (measurableSet_slab α β)))
    (by norm_num)

include h1 in
/-- **The dyadic limit with gain**: `‖W‖⁴ ≤ 32 K C_L⁴ (β−α)^{1/4} ‖F‖_{4/3}⁴`. -/
theorem norm_Wlim_pow : ‖Wlim hαβ hlen F‖ ^ 4 ≤
    32 * Kg L * CL L ^ 4 * (β - α) ^ (4⁻¹ : ℝ) * ‖F‖ ^ 4 := by
  have hA := Aq_nonneg F hαβ
  have h1' := norm_Wlim_le hαβ hlen h1 F
  have h4 : ‖Wlim hαβ hlen F‖ ^ 4 ≤ 256 * Aq F := by
    calc ‖Wlim hαβ hlen F‖ ^ 4 ≤ (4 * Aq F ^ (4⁻¹ : ℝ)) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1' 4
      _ = 256 * Aq F := by
          rw [mul_pow, show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
            Real.rpow_inv_natCast_pow hA (by norm_num)]
          norm_num
  have hm3 : mass F β ^ 3 ≤ ‖F‖ ^ 4 := by
    have hm := mass_le_norm hαβ F
    have := pow_le_pow_left₀ (mass_nonneg F β) hm 3
    refine this.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  refine h4.trans ?_
  unfold Aq
  have hK := Kg_nonneg (L := L)
  have hC := CL_nonneg (L := L)
  have hT : 0 ≤ (β - α) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by linarith) _
  have hK' : 0 ≤ Kg L * (β - α) ^ (4⁻¹ : ℝ) * CL L ^ 4 := by positivity
  calc 256 * (Kg L * (β - α) ^ (4⁻¹ : ℝ) * CL L ^ 4 * mass F β ^ 3 / 8)
      = 32 * (Kg L * (β - α) ^ (4⁻¹ : ℝ) * CL L ^ 4) * mass F β ^ 3 := by ring
    _ ≤ 32 * (Kg L * (β - α) ^ (4⁻¹ : ℝ) * CL L ^ 4) * ‖F‖ ^ 4 := by gcongr
    _ = 32 * Kg L * CL L ^ 4 * (β - α) ^ (4⁻¹ : ℝ) * ‖F‖ ^ 4 := by ring

#print axioms tendsto_Wlim
#print axioms norm_Wlim_pow

end Limit

/-! ## Slices of the step objects and of the limit -/

lemma coeFn_finsetSum_L2 {ι : Type*} (s : Finset ι) (f : ι → HL L) :
    (⇑(∑ i ∈ s, f i) : AddCircle L → ℂ) =ᵐ[volume] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

section Slices

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1)
  (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

/-- The level-`N` cell `(τ_{N,j}, τ_{N,j+1}]`. -/
abbrev cell (N j : ℕ) : Set ℝ := Set.Ioc (tp F N j) (tp F N (j + 1))

/-- `E_N(t) = Σ_j 1_{cell_j}(t) U(t) R(τ_{N,j})` in `L²`. -/
def EN (N : ℕ) (t : ℝ) : HL L :=
  ∑ j ∈ Finset.range (2 ^ N), (cell F N j).indicator (fun t => evol (Rt hαβ hlen F (tp F N j)) t) t

lemma stepObj_slice (N : ℕ) : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
    (fun x => stepObj hαβ hlen F N (t, x)) =ᵐ[volume] (EN hαβ hlen F N t : AddCircle L → ℂ) := by
  have hsum := Measure.ae_ae_of_ae_prod (coeFn_finsetSum (L := L) (Finset.range (2 ^ N))
    fun j => piece α β (tp F N j) (tp F N (j + 1)) (Rt hαβ hlen F (tp F N j)))
  have hpieces : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), ∀ j ∈ Finset.range (2 ^ N),
      (fun x => piece α β (tp F N j) (tp F N (j + 1)) (Rt hαβ hlen F (tp F N j)) (t, x)) =ᵐ[volume]
        fun x => (cell F N j).indicator
          (fun t => (evol (Rt hαβ hlen F (tp F N j)) t : AddCircle L → ℂ) x) t :=
    (eventually_all_finset _).mpr fun j _ => piece_slice hαβ hlen _ _ _
  filter_upwards [hsum, hpieces] with t ht1 ht2
  have ht2' := (eventually_all_finset _).mpr ht2
  filter_upwards [ht1, ht2', coeFn_finsetSum_L2 (Finset.range (2 ^ N))
    (fun j => (cell F N j).indicator (fun t => evol (Rt hαβ hlen F (tp F N j)) t) t),
    Lp.coeFn_zero ℂ 2 (volume : Measure (AddCircle L))] with x hx1 hx2 hx3 hx4
  show stepObj hαβ hlen F N (t, x) = (EN hαβ hlen F N t : AddCircle L → ℂ) x
  rw [EN, hx3]
  unfold stepObj
  rw [hx1]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hx2 j hj]
  by_cases htc : t ∈ cell F N j
  · rw [Set.indicator_of_mem htc, Set.indicator_of_mem htc]
  · rw [Set.indicator_of_notMem htc, Set.indicator_of_notMem htc, hx4]; rfl

include hαβ in
lemma tp_top (N : ℕ) : tp F N (2 ^ N) = β := by
  have hl : lev F N (2 ^ N) = mass F β := by unfold lev; push_cast; field_simp
  refine le_antisymm (tp_mem hαβ F N _).2 ?_
  unfold tp
  rw [hl]
  exact le_csSup (tau_set_bdd F _) ⟨⟨hαβ, le_rfl⟩, le_rfl⟩

lemma cover (N : ℕ) {t : ℝ} (h0 : tp F N 0 < t) :
    ∀ m : ℕ, t ≤ tp F N m → ∃ j < m, t ∈ cell F N j := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (not_le.mpr h0)
  | succ m ih =>
    intro h
    by_cases hm : t ≤ tp F N m
    · obtain ⟨j, hj, hjt⟩ := ih hm
      exact ⟨j, by omega, hjt⟩
    · exact ⟨m, by omega, not_le.mp hm, h⟩

include hαβ in
lemma cells_disjoint (N : ℕ) {i j : ℕ} (hij : i ≠ j) : Disjoint (cell F N i) (cell F N j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Set.Ioc_disjoint_Ioc_of_le (tp_mono hαβ F N (by omega))
  · exact (Set.Ioc_disjoint_Ioc_of_le (tp_mono hαβ F N (by omega))).symm

include hαβ in
/-- `‖E_N(t) − U(t)R(t)‖ ≤ C_L (M/2^N)^{3/4}` for `t ∈ (α, β]`. -/
lemma EN_close (N : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc α β) :
    ‖EN hαβ hlen F N t - evol (Rt hαβ hlen F t) t‖ ≤
      CL L * (mass F β / 2 ^ N) ^ (3 / 4 : ℝ) := by
  have hC := CL_nonneg (L := L)
  have hM := mass_nonneg F β
  by_cases hex : ∃ j ∈ Finset.range (2 ^ N), t ∈ cell F N j
  · obtain ⟨j0, hj0, htj⟩ := hex
    have hj0' : j0 < 2 ^ N := Finset.mem_range.mp hj0
    have hz : ∀ j ∈ Finset.range (2 ^ N), j ≠ j0 →
        (cell F N j).indicator (fun t => evol (Rt hαβ hlen F (tp F N j)) t) t = 0 := by
      intro j _ hj
      exact Set.indicator_of_notMem (fun htj' =>
        Set.disjoint_left.mp (cells_disjoint hαβ F N hj) htj' htj) _
    rw [EN, Finset.sum_eq_single_of_mem j0 hj0 hz, Set.indicator_of_mem htj, ← evol_sub,
      norm_evol, norm_sub_rev]
    have hc : α ≤ tp F N j0 := (tp_mem hαβ F N j0).1
    have hb := norm_Rt_sub hαβ hlen F hc htj.1.le
    have hmt : mass F t ≤ lev F N (j0 + 1) := by
      rw [← mass_tp hαβ F N (j0 + 1) (by omega)]
      exact mass_mono F (hc.trans htj.1.le) htj.2
    rw [mass_tp hαβ F N j0 (by omega)] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC)
    have hmono := mass_mono F hc htj.1.le
    have hmtp : mass F (tp F N j0) = lev F N j0 := mass_tp hαβ F N j0 (by omega)
    refine Real.rpow_le_rpow (by linarith) ?_ (by norm_num)
    have : lev F N (j0 + 1) - lev F N j0 = mass F β / 2 ^ N := by unfold lev; push_cast; ring
    linarith
  · simp only [not_exists, not_and] at hex
    have hE : EN hαβ hlen F N t = 0 :=
      Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hex j hj) _
    rw [hE, zero_sub, norm_neg, norm_evol]
    -- `t` lies below the first cell, where the mass vanishes
    have hle : t ≤ tp F N 0 := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨j, hj, hjt⟩ := cover F N hlt (2 ^ N) (by rw [tp_top hαβ F N]; exact ht.2)
      exact hex j (Finset.mem_range.mpr hj) hjt
    have hm0 : mass F t = 0 := by
      have := mass_mono F ht.1.le hle
      rw [mass_tp hαβ F N 0 (by positivity), show lev F N 0 = 0 by simp [lev]] at this
      linarith [mass_nonneg F t]
    have hb := norm_Rt_sub hαβ hlen F (le_refl α) ht.1.le
    rw [hm0, mass_self, sub_zero, Real.zero_rpow (by norm_num), mul_zero] at hb
    have h2 : ‖Rt hαβ hlen F t‖ ≤ ‖Rt hαβ hlen F t - Rt hαβ hlen F α‖ + ‖Rt hαβ hlen F α‖ := by
      calc ‖Rt hαβ hlen F t‖ = ‖(Rt hαβ hlen F t - Rt hαβ hlen F α) + Rt hαβ hlen F α‖ := by
            abel_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_Rt_alpha] at h2
    have : 0 ≤ CL L * (mass F β / 2 ^ N) ^ (3 / 4 : ℝ) :=
      mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
    linarith

lemma tendsto_bound : Tendsto (fun N : ℕ => CL L * (mass F β / 2 ^ N) ^ (3 / 4 : ℝ)) atTop
    (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => mass F β / 2 ^ N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h2 : Tendsto (fun N : ℕ => (mass F β / 2 ^ N) ^ (3 / 4 : ℝ)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (3 / 4) (Or.inr (by norm_num))).tendsto).comp h1
    rwa [Real.zero_rpow (by norm_num)] at this
  simpa using h2.const_mul (CL L)

include h1 in
/-- **Slices of the dyadic limit**: for a.e. `t ∈ J`, `W(t, ·) = U(t) S_{(α,t]} F`. -/
theorem Wlim_slice : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
    (fun x => Wlim hαβ hlen F (t, x)) =ᵐ[volume] (evol (Rt hαβ hlen F t) t : AddCircle L → ℂ) := by
  have hm : TendstoInMeasure (μJ α β)
      (fun N => (stepObj hαβ hlen F N : ℝ × AddCircle L → ℂ)) atTop (Wlim hαβ hlen F) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (tendsto_Wlim hαβ hlen h1 F))
  obtain ⟨ns, hns_mono, hns⟩ := hm.exists_seq_tendsto_ae
  have hslices : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), ∀ k,
      (fun x => stepObj hαβ hlen F (ns k) (t, x)) =ᵐ[volume]
        (EN hαβ hlen F (ns k) t : AddCircle L → ℂ) :=
    ae_all_iff.mpr fun k => stepObj_slice hαβ hlen F (ns k)
  filter_upwards [Measure.ae_ae_of_ae_prod hns, hslices, ae_restrict_mem measurableSet_Ioc]
    with t ht hts htJ
  have hL2 : Tendsto (fun k => EN hαβ hlen F (ns k) t) atTop (𝓝 (evol (Rt hαβ hlen F t) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => EN_close hαβ hlen F (ns k) htJ)
      ((tendsto_bound F).comp hns_mono.tendsto_atTop)
  have hm2 : TendstoInMeasure (volume : Measure (AddCircle L))
      (fun k => (EN hαβ hlen F (ns k) t : AddCircle L → ℂ)) atTop
      (evol (Rt hαβ hlen F t) t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hL2)
  obtain ⟨ms, hms_mono, hms⟩ := hm2.exists_seq_tendsto_ae
  have hts' := ae_all_iff.mpr hts
  filter_upwards [ht, hms, hts'] with x hx1 hx2 hx3
  have hA : Tendsto (fun j => stepObj hαβ hlen F (ns (ms j)) (t, x)) atTop
      (𝓝 (Wlim hαβ hlen F (t, x))) := hx1.comp hms_mono.tendsto_atTop
  have hB : Tendsto (fun j => stepObj hαβ hlen F (ns (ms j)) (t, x)) atTop
      (𝓝 ((evol (Rt hαβ hlen F t) t : AddCircle L → ℂ) x)) := by
    refine hx2.congr fun j => ?_
    exact (hx3 (ms j)).symm
  exact tendsto_nhds_unique hA hB

#print axioms EN_close
#print axioms Wlim_slice

end Slices

/-! ## The retarded Duhamel estimate `L^{4/3} → L⁴` with time gain -/

section Final

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (h1 : β - α ≤ 1)
  (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

lemma norm_Rt_le (t : ℝ) : ‖Rt hαβ hlen F t‖ ≤ CL L * ‖F‖ := by
  refine (norm_rep_le hαβ hlen _).trans (mul_le_mul_of_nonneg_left ?_ CL_nonneg)
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp F).ne
    (eLpNorm_indicator_le _ (measurableSet_Ioc.prod MeasurableSet.univ))

/-- The retarded Duhamel term `V(t) = ∫_a^t U(t−s)F(s) ds` as an element of `L⁴(J × 𝕋_L)`:
`W − U(·) S_{(α,a]}F`. -/
def Vst (a : ℝ) : Lp ℂ 4 (μJ (L := L) α β) := Wlim hαβ hlen F - freeL4 α β (Rt hαβ hlen F a)

include h1 in
/-- Slices of the space-time Duhamel term: for a.e. `t ∈ J`, `Vst(t, ·) = V(t)` (DD1's duality
Duhamel map). -/
theorem Vst_slice (a : ℝ) : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
    (fun x => Vst hαβ hlen F a (t, x)) =ᵐ[volume] (V hαβ hlen F a t : AddCircle L → ℂ) := by
  have hsub := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_sub (Wlim hαβ hlen F) (freeL4 α β (Rt hαβ hlen F a)))
  filter_upwards [hsub, Wlim_slice hαβ hlen h1 F, freeL4_slice hαβ hlen (Rt hαβ hlen F a)]
    with t h1' h2 h3
  filter_upwards [h1', h2, h3, Lp.coeFn_sub (evol (Rt hαβ hlen F t) t)
    (evol (Rt hαβ hlen F a) t)] with x hx1 hx2 hx3 hx4
  show Vst hαβ hlen F a (t, x) = (V hαβ hlen F a t : AddCircle L → ℂ) x
  rw [Vst, hx1, Pi.sub_apply, hx2, hx3, V, Sop, evol_sub, hx4, Pi.sub_apply]

include h1 in
/-- **Route Y stage (ii): the retarded Duhamel estimate with time gain.** For `α < β`,
`β − α ≤ min(1, T_L)`, every `F ∈ L^{4/3}(J × 𝕋_L)` and base `a`, the space-time term `Vst`
(whose slices are `V(t) = ∫_a^t U(t−s)F(s) ds`) satisfies
`‖Vst‖_{L⁴} ≤ (32 K C_L⁴ (β−α)^{1/4} ‖F‖⁴)^{1/4} + K^{1/4} (β−α)^{1/16} C_L ‖F‖_{4/3}`. -/
theorem norm_Vst_le (hlt : α < β) (a : ℝ) :
    ‖Vst hαβ hlen F a‖ ≤ (32 * Kg L * CL L ^ 4 * (β - α) ^ (4⁻¹ : ℝ) * ‖F‖ ^ 4) ^ (4⁻¹ : ℝ) +
      Kg L ^ (4⁻¹ : ℝ) * (β - α) ^ (16⁻¹ : ℝ) * (CL L * ‖F‖) := by
  have hW : ‖Wlim hαβ hlen F‖ ≤
      (32 * Kg L * CL L ^ 4 * (β - α) ^ (4⁻¹ : ℝ) * ‖F‖ ^ 4) ^ (4⁻¹ : ℝ) := by
    have h4 := norm_Wlim_pow hαβ hlen h1 F
    have hr : ‖Wlim hαβ hlen F‖ = (‖Wlim hαβ hlen F‖ ^ 4) ^ (4⁻¹ : ℝ) := by
      rw [show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (norm_nonneg _)
        (by norm_num)]
    rw [hr]
    exact Real.rpow_le_rpow (by positivity) h4 (by norm_num)
  have hfree : ‖freeL4 α β (Rt hαβ hlen F a)‖ ≤
      Kg L ^ (4⁻¹ : ℝ) * (β - α) ^ (16⁻¹ : ℝ) * ‖Rt hαβ hlen F a‖ := by
    have hg := gain_L2_norm (Rt hαβ hlen F a) α (T := β - α) (by linarith) h1 (by linarith)
    rw [show α + (β - α) = β by ring] at hg
    exact hg
  have hR := norm_Rt_le hαβ hlen F a
  have hc : 0 ≤ Kg L ^ (4⁻¹ : ℝ) * (β - α) ^ (16⁻¹ : ℝ) :=
    mul_nonneg (Real.rpow_nonneg Kg_nonneg _) (Real.rpow_nonneg (by linarith) _)
  calc ‖Vst hαβ hlen F a‖ ≤ ‖Wlim hαβ hlen F‖ + ‖freeL4 α β (Rt hαβ hlen F a)‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hW (hfree.trans (mul_le_mul_of_nonneg_left hR hc))

#print axioms Vst_slice
#print axioms norm_Vst_le

end Final

end QuantumNLS.DuhamelL4Limit
