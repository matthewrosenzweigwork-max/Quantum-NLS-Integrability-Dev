import QuantumNLS.F04Regularity

/-!
# F04:thm-global (R-169AABCC): global `H^1` flow and regular approximation

Source: `source/chapters/foundations/F04.tex`, Theorem `F04:thm-global` (lines 277-297) and its
proof (lines 299-350).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Topology ComplexConjugate InnerProductSpace
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity

namespace QuantumNLS.F04Global

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Fourier truncation `P_N` -/

/-- The window `{n : |n| ≤ N}`. -/
def win (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

lemma mem_win (N : ℕ) (n : ℤ) : n ∈ win N ↔ |n| ≤ N := by
  rw [win, Finset.mem_Icc, abs_le]

lemma win_mono : Monotone win := fun a b hab =>
  Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)

lemma win_exh (m : ℤ) : ∃ N, m ∈ win N := ⟨m.natAbs, by simp only [win, Finset.mem_Icc]; omega⟩

/-- `P_N a`: Fourier projection onto `|n| ≤ N`; it lies in `H^3`. -/
def PN (N : ℕ) (a : h04 L 1) : h04 L 3 :=
  WSeq.mk _ (fun n => if n ∈ win N then a.val n else 0) (by
    refine summable_of_ne_finset_zero (s := win N) fun n hn => ?_
    simp [hn])

@[simp] lemma PN_val (N : ℕ) (a : h04 L 1) (n : ℤ) :
    (PN N a).val n = if n ∈ win N then a.val n else 0 := rfl

lemma PN_norm_le (N : ℕ) (a : h04 L 1) : ‖m31 (PN N a)‖ ≤ ‖a‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun n => ?_) (WSeq.summable _) a.summable
  simp only [m31_val, PN_val]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero, mul_zero]
    exact mul_nonneg ((f04W L 1).pos n).le (sq_nonneg _)

lemma PN_sub_val (N : ℕ) (a : h04 L 1) (n : ℤ) :
    (m31 (PN N a) - a).val n = if n ∈ win N then 0 else -a.val n := by
  rw [WSeq.val_sub, Pi.sub_apply, m31_val, PN_val]
  split_ifs
  · exact sub_self _
  · exact zero_sub _

/-- The tail terms `w_n |(P_N a − a)_n|²`. -/
def tailTerm (a : h04 L 1) (N : ℕ) (n : ℤ) : ℝ := (f04W L 1).w n * ‖(m31 (PN N a) - a).val n‖ ^ 2

lemma tailTerm_eq (a : h04 L 1) (N : ℕ) (n : ℤ) :
    tailTerm a N n = if n ∈ win N then 0 else (f04W L 1).w n * ‖a.val n‖ ^ 2 := by
  rw [tailTerm, PN_sub_val]
  split_ifs
  · rw [norm_zero, zero_pow two_ne_zero, mul_zero]
  · rw [norm_neg]

lemma tailTerm_tendsto (a : h04 L 1) (n : ℤ) :
    Tendsto (fun N => tailTerm a N n) atTop (𝓝 0) := by
  obtain ⟨N0, hN0⟩ := win_exh n
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N0] with N hN
  rw [tailTerm_eq]
  simp only [win_mono hN hN0, ↓reduceIte]

lemma tailTerm_le (a : h04 L 1) (N : ℕ) (n : ℤ) :
    ‖tailTerm a N n‖ ≤ (f04W L 1).w n * ‖a.val n‖ ^ 2 := by
  have h0 : 0 ≤ (f04W L 1).w n * ‖a.val n‖ ^ 2 := mul_nonneg ((f04W L 1).pos n).le (sq_nonneg _)
  rw [tailTerm_eq]
  split_ifs
  · rw [norm_zero]; exact h0
  · rw [Real.norm_of_nonneg h0]

lemma norm_sq_PN_sub (a : h04 L 1) (N : ℕ) : ‖m31 (PN N a) - a‖ ^ 2 = ∑' n, tailTerm a N n :=
  norm_sq_eq_tsum _ _

lemma PN_tendsto (a : h04 L 1) : Tendsto (fun N => m31 (PN N a)) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (G := ℝ)
    (f := fun (N : ℕ) n => tailTerm a N n) (g := fun _ => 0)
    (bound := fun n => (f04W L 1).w n * ‖a.val n‖ ^ 2) a.summable (tailTerm_tendsto a)
    (Eventually.of_forall fun N n => tailTerm_le a N n)
  rw [tsum_zero] at h
  have hsq : Tendsto (fun N => ‖m31 (PN N a) - a‖ ^ 2) atTop (𝓝 0) :=
    h.congr fun N => (norm_sq_PN_sub a N).symm
  have h2 := hsq.sqrt
  rw [Real.sqrt_zero] at h2
  exact h2.congr fun N => Real.sqrt_sq (norm_nonneg _)

#print axioms PN_norm_le
#print axioms tailTerm_le
#print axioms PN_tendsto

/-! ## 2. Regular solutions viewed in `H^1` -/

lemma val_m31 (a : h04 L 3) : (m31 a).val = a.val := funext (m31_val a)

lemma m31_Sgrp (t : ℝ) (a : h04 L 3) : m31 (Sgrp 3 t a) = Sgrp 1 t (m31 a) :=
  WSeq.ext (funext fun n => by simp only [m31_val, Sgrp_val])

lemma Fh_val' {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) : (Fh hs a).val = coeff L (nlRep L a.val) := rfl

lemma m31_Fh (a : h04 L 3) : m31 (Fh hs3 a) = Fh (le_refl (1 : ℝ)) (m31 a) :=
  WSeq.ext (by rw [val_m31, Fh_val', Fh_val', val_m31])

/-- An `H^3` mild solution is an `H^1` mild solution. -/
lemma mild31 {κ : ℝ} {I : Set ℝ} {v0 : h04 L 3} {v : ℝ → h04 L 3} (hv : IsMild hs3 κ I v0 v) :
    IsMild (le_refl (1 : ℝ)) κ I (m31 v0) (fun t => m31 (v t)) := by
  refine ⟨hv.zero_mem, hv.ordConnected, (m31 (L := L)).continuous.comp_continuousOn hv.cont,
    fun t ht => ?_⟩
  rw [hv.duhamel_eq t ht]
  unfold duhamel
  have hi := integrable_duhamel hs3 hv.ordConnected hv.cont t 0 t hv.zero_mem ht
  have e : ∫ r in (0 : ℝ)..t, m31 (Sgrp 3 (t - r) (Fh hs3 (v r))) =
      ∫ r in (0 : ℝ)..t, Sgrp 1 (t - r) (Fh (le_refl (1 : ℝ)) (m31 (v r))) :=
    intervalIntegral.integral_congr fun r _ => by simp only [m31_Sgrp, m31_Fh]
  rw [map_sub, map_smul, m31_Sgrp, ← (m31 (L := L)).intervalIntegral_comp_comm hi, e]

#print axioms mild31

/-! ## 3. Continuity of the invariants and the uniform energy bound -/

lemma continuous_mass : Continuous (mass (L := L)) := by
  show Continuous fun a => ‖m10 a‖ ^ 2
  exact ((m10 (L := L)).continuous.norm).pow 2

lemma continuous_kin : Continuous (kin (L := L)) := by
  show Continuous fun a => ‖D a‖ ^ 2
  exact ((D (L := L)).continuous.norm).pow 2

lemma continuous_quart : Continuous (quart (L := L)) := by
  have e : (quart (L := L)) =
      fun a => (intCLM (S1 a * star (S1 a) * S1 a * star (S1 a))).re := by
    funext a; rw [intCLM_P, Complex.ofReal_re]
  rw [e]
  have hS := (S1 (L := L)).continuous
  exact Complex.continuous_re.comp ((intCLM (L := L)).continuous.comp
    (((hS.mul hS.star).mul hS).mul hS.star))

lemma continuous_energy (κ : ℝ) : Continuous (energy (L := L) κ) := by
  show Continuous fun a => kin a + κ * quart a
  exact continuous_kin.add (continuous_const.mul continuous_quart)

lemma norm_S1_le (a : h04 L 1) (x : AddCircle L) : ‖S1 a x‖ ≤ cL L * ‖a‖ := by
  have h3 : ‖(S1 (L := L))‖ ≤ cL L := LinearMap.mkContinuous_norm_le _ (cL_nonneg L) _
  calc ‖S1 a x‖ ≤ ‖S1 a‖ := (S1 a).norm_coe_le_norm x
    _ ≤ ‖S1 (L := L)‖ * ‖a‖ := (S1 (L := L)).le_opNorm a
    _ ≤ cL L * ‖a‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

/-- `‖f‖_4^4 ≤ ‖f‖_∞² ‖f‖_2² ≤ c_L² ‖f‖_{H¹}⁴`. -/
lemma quart_le (a : h04 L 1) : quart a ≤ cL L ^ 2 * ‖a‖ ^ 4 := by
  have hm : mass a ≤ ‖a‖ ^ 2 := by
    rw [norm_sq_h1]; have : 0 ≤ kin a := sq_nonneg _; linarith
  have hpt : ∀ x, ‖S1 a x‖ ^ 4 ≤ (cL L * ‖a‖) ^ 2 * ‖S1 a x‖ ^ 2 := fun x => by
    have h0 := norm_nonneg (S1 a x)
    have h2 : ‖S1 a x‖ ^ 2 ≤ (cL L * ‖a‖) ^ 2 := pow_le_pow_left₀ h0 (norm_S1_le a x) 2
    nlinarith [sq_nonneg ‖S1 a x‖]
  have hc : Continuous fun x => ‖S1 a x‖ := (S1 a).continuous.norm
  have hint : ∀ k : ℕ, Integrable (fun x => ‖S1 a x‖ ^ k) := fun k =>
    (hc.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc quart a = ∫ x, ‖S1 a x‖ ^ 4 := rfl
    _ ≤ ∫ x, (cL L * ‖a‖) ^ 2 * ‖S1 a x‖ ^ 2 :=
        integral_mono (hint 4) ((hint 2).const_mul _) hpt
    _ = (cL L * ‖a‖) ^ 2 * mass a := by rw [integral_const_mul, mass_eq_integral]
    _ ≤ (cL L * ‖a‖) ^ 2 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = cL L ^ 2 * ‖a‖ ^ 4 := by ring

/-- `K_R² = R² + κ c_L² R⁴` (`F04:eq-uniform-energy`). -/
def KR2 (κ R : ℝ) : ℝ := R ^ 2 + κ * cL L ^ 2 * R ^ 4

lemma KR2_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (R : ℝ) : 0 ≤ KR2 (L := L) κ R := by
  unfold KR2; positivity

/-- **`F04:eq-uniform-energy`**: `M(f) + E(f) = ‖f‖²_{H¹} + κ‖f‖_4^4 ≤ K_R²` for `‖f‖_{H¹} ≤ R`. -/
lemma ME_le {κ R : ℝ} (hκ : 0 ≤ κ) {a : h04 L 1} (ha : ‖a‖ ≤ R) :
    mass a + energy κ a ≤ KR2 (L := L) κ R := by
  have h1 : mass a + energy κ a = ‖a‖ ^ 2 + κ * quart a := by
    rw [norm_sq_h1, energy]; ring
  rw [h1, KR2]
  have h0 := norm_nonneg a
  have hR2 : ‖a‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 ha 2
  have hR4 : ‖a‖ ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ h0 ha 4
  have hq : κ * quart a ≤ κ * (cL L ^ 2 * R ^ 4) :=
    mul_le_mul_of_nonneg_left ((quart_le a).trans (mul_le_mul_of_nonneg_left hR4 (sq_nonneg _))) hκ
  nlinarith

#print axioms continuous_quart
#print axioms quart_le
#print axioms ME_le

/-! ## 4. Conservation and globality in `H^1` -/

section Flow

variable {κ : ℝ}

/-- The regular approximant `t ↦ u_N(t)` (solution from `P_N u₀`), viewed in `H^1`. -/
def vN (κ : ℝ) (N : ℕ) (u0 : h04 L 1) (t : ℝ) : h04 L 1 := m31 (umax hs3 κ (PN N u0) t)

lemma vN_mild (hκ : 0 ≤ κ) (N : ℕ) (u0 : h04 L 1) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ (m31 (PN N u0)) (vN κ N u0) :=
  mild31 (lem_regular hκ (PN N u0)).1

lemma vN_mass (hκ : 0 ≤ κ) (N : ℕ) (u0 : h04 L 1) (t : ℝ) :
    mass (vN κ N u0 t) = mass (m31 (PN N u0)) :=
  mass_const_Imax hκ (PN N u0) (by rw [Imax_eq_univ hκ]; trivial)

lemma vN_energy (hκ : 0 ≤ κ) (N : ℕ) (u0 : h04 L 1) (t : ℝ) :
    energy κ (vN κ N u0 t) = energy κ (m31 (PN N u0)) :=
  energy_const_Imax hκ (PN N u0) (by rw [Imax_eq_univ hκ]; trivial)

lemma vN_bound (hκ : 0 ≤ κ) (N : ℕ) (u0 : h04 L 1) (t : ℝ) :
    ‖vN κ N u0 t‖ ≤ Real.sqrt (KR2 (L := L) κ ‖u0‖) := by
  apply Real.le_sqrt_of_sq_le
  have := norm_sq_le_mass_energy hκ (vN κ N u0 t)
  rw [vN_mass hκ, vN_energy hκ] at this
  exact this.trans (ME_le hκ (PN_norm_le N u0))

/-- On the maximal `H^1` interval, `u_N(t) → u(t)` in `H^1` (stability `F04:eq-stability`). -/
lemma vN_tendsto (hκ : 0 ≤ κ) (u0 : h04 L 1) {t : ℝ} (ht : t ∈ Imax (le_refl (1 : ℝ)) κ u0) :
    Tendsto (fun N => vN κ N u0 t) atTop (𝓝 (umax (le_refl (1 : ℝ)) κ u0 t)) := by
  have hu := umax_mild (hs := le_refl (1 : ℝ)) hκ u0
  set u := umax (le_refl (1 : ℝ)) κ u0
  set J := Set.uIcc 0 t
  have hJ : J ⊆ Imax (le_refl (1 : ℝ)) κ u0 := hu.ordConnected.uIcc_subset hu.zero_mem ht
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hu.cont.mono hJ)
  set K := max B (Real.sqrt (KR2 (L := L) κ ‖u0‖))
  have hK : ∀ N, ∀ r ∈ J, ‖vN κ N u0 r‖ ≤ K ∧ ‖u r‖ ≤ K := fun N r hr =>
    ⟨(vN_bound hκ N u0 r).trans (le_max_right _ _), (hB r hr).trans (le_max_left _ _)⟩
  set C := Real.exp (4 * κ * Cs L 1 * K ^ 2 * |t - 0|)
  have hst : ∀ N, ‖vN κ N u0 t - u t‖ ≤ C * ‖m31 (PN N u0) - u0‖ := by
    intro N
    have h1 := (vN_mild hκ N u0).mono (Set.subset_univ J) Set.left_mem_uIcc Set.ordConnected_uIcc
    have h2 := hu.mono hJ Set.left_mem_uIcc Set.ordConnected_uIcc
    have := stability (le_refl (1 : ℝ)) hκ h1 h2 (hK N) Set.left_mem_uIcc Set.right_mem_uIcc
    rwa [h1.at_zero, h2.at_zero] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hP := (tendsto_iff_norm_sub_tendsto_zero.mp (PN_tendsto u0)).const_mul C
  rw [mul_zero] at hP
  exact squeeze_zero (fun _ => norm_nonneg _) hst hP

lemma mass_cons1 (hκ : 0 ≤ κ) (u0 : h04 L 1) {t : ℝ} (ht : t ∈ Imax (le_refl (1 : ℝ)) κ u0) :
    mass (umax (le_refl (1 : ℝ)) κ u0 t) = mass u0 := by
  have h1 := (continuous_mass.tendsto _).comp (vN_tendsto hκ u0 ht)
  have h2 := (continuous_mass.tendsto _).comp (PN_tendsto u0)
  have e : (mass ∘ fun N => vN κ N u0 t) = (mass ∘ fun N => m31 (PN N u0)) :=
    funext fun N => vN_mass hκ N u0 t
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

lemma energy_cons1 (hκ : 0 ≤ κ) (u0 : h04 L 1) {t : ℝ} (ht : t ∈ Imax (le_refl (1 : ℝ)) κ u0) :
    energy κ (umax (le_refl (1 : ℝ)) κ u0 t) = energy κ u0 := by
  have h1 := ((continuous_energy κ).tendsto _).comp (vN_tendsto hκ u0 ht)
  have h2 := ((continuous_energy κ).tendsto _).comp (PN_tendsto u0)
  have e : (energy κ ∘ fun N => vN κ N u0 t) = (energy κ ∘ fun N => m31 (PN N u0)) :=
    funext fun N => vN_energy hκ N u0 t
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

lemma bound1 (hκ : 0 ≤ κ) (u0 : h04 L 1) {t : ℝ} (ht : t ∈ Imax (le_refl (1 : ℝ)) κ u0) :
    ‖umax (le_refl (1 : ℝ)) κ u0 t‖ ^ 2 ≤ mass u0 + energy κ u0 := by
  have := norm_sq_le_mass_energy hκ (umax (le_refl (1 : ℝ)) κ u0 t)
  rwa [mass_cons1 hκ u0 ht, energy_cons1 hκ u0 ht] at this

/-- **Globality in `H^1`**. -/
lemma Imax1_eq_univ (hκ : 0 ≤ κ) (u0 : h04 L 1) : Imax (le_refl (1 : ℝ)) κ u0 = Set.univ := by
  set I := Imax (le_refl (1 : ℝ)) κ u0
  set M := Real.sqrt (mass u0 + energy κ u0)
  have hcap : ∀ t ∈ I, ‖umax (le_refl (1 : ℝ)) κ u0 t‖ ≤ M := fun t ht =>
    Real.le_sqrt_of_sq_le (bound1 hκ u0 ht)
  have hA : ¬ BddAbove I := by
    intro hb
    obtain ⟨t, htI, -, ht2⟩ := blowup_right (hs := le_refl (1 : ℝ)) hκ u0 hb M 1 one_pos
    linarith [hcap t htI]
  have hA' : ¬ BddBelow I := by
    intro hb
    obtain ⟨t, htI, -, ht2⟩ := blowup_left (hs := le_refl (1 : ℝ)) hκ u0 hb M 1 one_pos
    linarith [hcap t htI]
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨y, hyI, hxy⟩ := not_bddAbove_iff.mp hA x
  obtain ⟨z, hzI, hzx⟩ := not_bddBelow_iff.mp hA' x
  exact (Imax_ordConnected u0).out hzI hyI ⟨hzx.le, hxy.le⟩

lemma umax1_mild (hκ : 0 ≤ κ) (u0 : h04 L 1) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ u0 (umax (le_refl (1 : ℝ)) κ u0) := by
  have hu := umax_mild (hs := le_refl (1 : ℝ)) hκ u0
  rw [Imax1_eq_univ hκ u0] at hu
  exact hu

#print axioms vN_tendsto
#print axioms Imax1_eq_univ

/-! ## 5. Lipschitz dependence and regular approximation -/

/-- **Lipschitz dependence on bounded sets**: for `‖u₀‖, ‖v₀‖ ≤ R` and `|t| ≤ T`,
`‖u(t) − v(t)‖_{H¹} ≤ e^{4κ C_{1,L} K_R² T} ‖u₀ − v₀‖_{H¹}`. -/
theorem lipschitz_bounded (hκ : 0 ≤ κ) {R T : ℝ} {u0 v0 : h04 L 1} (hu0 : ‖u0‖ ≤ R)
    (hv0 : ‖v0‖ ≤ R) {t : ℝ} (ht : |t| ≤ T) :
    ‖umax (le_refl (1 : ℝ)) κ u0 t - umax (le_refl (1 : ℝ)) κ v0 t‖ ≤
      Real.exp (4 * κ * Cs L 1 * KR2 (L := L) κ R * T) * ‖u0 - v0‖ := by
  have hu := umax1_mild hκ u0
  have hv := umax1_mild hκ v0
  set K := Real.sqrt (KR2 (L := L) κ R)
  have hb : ∀ w0 : h04 L 1, ‖w0‖ ≤ R → ∀ r, ‖umax (le_refl (1 : ℝ)) κ w0 r‖ ≤ K := by
    intro w0 hw0 r
    have hmem : r ∈ Imax (le_refl (1 : ℝ)) κ w0 := by rw [Imax1_eq_univ hκ w0]; trivial
    exact Real.le_sqrt_of_sq_le ((bound1 hκ w0 hmem).trans (ME_le hκ hw0))
  have := stability (le_refl (1 : ℝ)) hκ hu hv (fun r _ => ⟨hb u0 hu0 r, hb v0 hv0 r⟩)
    (Set.mem_univ 0) (Set.mem_univ t)
  rw [hu.at_zero, hv.at_zero, sub_zero, Real.sq_sqrt (KR2_nonneg hκ R)] at this
  refine this.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
  have hc : 0 ≤ 4 * κ * Cs L 1 * KR2 (L := L) κ R := by
    have := le_trans zero_le_one (one_le_Cs L 1)
    have := KR2_nonneg (L := L) hκ R
    positivity
  exact mul_le_mul_of_nonneg_left ht hc

/-- A regular solution, viewed in `H^1`, is the `H^1` solution from the same data. -/
lemma reg_eq (hκ : 0 ≤ κ) (w : h04 L 3) :
    (fun t => m31 (umax hs3 κ w t)) = umax (le_refl (1 : ℝ)) κ (m31 w) := by
  funext t
  exact mild_unique (le_refl (1 : ℝ)) hκ (mild31 (lem_regular hκ w).1) (umax1_mild hκ (m31 w)) t
    (Set.mem_univ t)

/-- **Regular approximation**: solutions of any `H^3` data converging to `u₀` in `H^1` converge to
`u` in `C([-T,T]; H^1)`. -/
theorem approx (hκ : 0 ≤ κ) {u0 : h04 L 1} {w : ℕ → h04 L 3}
    (hw : Tendsto (fun k => m31 (w k)) atTop (𝓝 u0)) (T : ℝ) :
    TendstoUniformlyOn (fun k t => m31 (umax hs3 κ (w k) t)) (umax (le_refl (1 : ℝ)) κ u0)
      atTop (Set.Icc (-T) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set R := ‖u0‖ + 1
  set C := Real.exp (4 * κ * Cs L 1 * KR2 (L := L) κ R * T)
  have hR : ∀ᶠ k in atTop, ‖m31 (w k)‖ ≤ R := by
    have := (continuous_norm.tendsto u0).comp hw
    exact (this.eventually (gt_mem_nhds (lt_add_one ‖u0‖))).mono fun k hk => hk.le
  have hsmall : ∀ᶠ k in atTop, C * ‖m31 (w k) - u0‖ < ε := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp hw).const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hε)
  filter_upwards [hR, hsmall] with k hk1 hk2
  intro t ht
  have hu0R : ‖u0‖ ≤ R := by simp only [R]; linarith
  have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hL := lipschitz_bounded hκ hk1 hu0R habs
  rw [dist_eq_norm, norm_sub_rev]
  show ‖m31 (umax hs3 κ (w k) t) - umax (le_refl (1 : ℝ)) κ u0 t‖ < ε
  rw [show m31 (umax hs3 κ (w k) t) = umax (le_refl (1 : ℝ)) κ (m31 (w k)) t from
    congrFun (reg_eq hκ (w k)) t]
  exact lt_of_le_of_lt hL hk2

#print axioms lipschitz_bounded
#print axioms approx

/-- **`F04:thm-global` (R-169AABCC)**. For `κ ≥ 0` and `u₀ ∈ H¹`, the maximal `H¹` mild solution
`u` is global, `u ∈ C(ℝ;H¹) ∩ C¹(ℝ;H^{-1})` and solves `i u_t = −∂_x²u + 2κ|u|²u` in `H^{-1}`;
it is unique among `C_tH¹` distributional (and mild) solutions; mass and energy are conserved and
`‖u(t)‖²_{H¹} ≤ M(u₀) + E(u₀)`; the Fourier-truncated solutions `u_N` (data `P_N u₀`) lie in
`C(ℝ;H³) ∩ C¹(ℝ;H¹)` and converge to `u` in `C([-T,T];H¹)`, as do the solutions of any sequence
of `H³` data converging to `u₀` in `H¹`. (Lipschitz dependence: `lipschitz_bounded`.) -/
theorem thm_global (hκ : 0 ≤ κ) (u0 : h04 L 1) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ u0 (umax (le_refl (1 : ℝ)) κ u0) ∧
    Continuous (umax (le_refl (1 : ℝ)) κ u0) ∧
    ContDiff ℝ 1 (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t)) ∧
    (∀ t, HasDerivAt (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t))
      (Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t)) t) ∧
    (∀ t, Complex.I • Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t) =
      lapOp 1 (umax (le_refl (1 : ℝ)) κ u0 t) +
        ((2 * κ : ℝ) : ℂ) • ι2 1 (Fh (le_refl (1 : ℝ)) (umax (le_refl (1 : ℝ)) κ u0 t))) ∧
    (∀ v : ℝ → h04 L 1, IsDistSol κ Set.univ v → v 0 = u0 →
      ∀ t, v t = umax (le_refl (1 : ℝ)) κ u0 t) ∧
    (∀ (J : Set ℝ) (v : ℝ → h04 L 1), IsMild (le_refl (1 : ℝ)) κ J u0 v →
      ∀ t ∈ J, v t = umax (le_refl (1 : ℝ)) κ u0 t) ∧
    (∀ t, ∫ x, ‖S1 (umax (le_refl (1 : ℝ)) κ u0 t) x‖ ^ 2 = ∫ x, ‖S1 u0 x‖ ^ 2) ∧
    (∀ t, ChargeEnergy.energyH1 κ (S1 (umax (le_refl (1 : ℝ)) κ u0 t)) =
      ChargeEnergy.energyH1 κ (S1 u0)) ∧
    (∀ t, ‖umax (le_refl (1 : ℝ)) κ u0 t‖ ^ 2 ≤
      (∫ x, ‖S1 u0 x‖ ^ 2) + ChargeEnergy.energyH1 κ (S1 u0)) ∧
    (∀ N : ℕ, Continuous (umax hs3 κ (PN N u0)) ∧
      ContDiff ℝ 1 (fun t => m31 (umax hs3 κ (PN N u0) t))) ∧
    (∀ T : ℝ, TendstoUniformlyOn (fun N t => m31 (umax hs3 κ (PN N u0) t))
      (umax (le_refl (1 : ℝ)) κ u0) atTop (Set.Icc (-T) T)) ∧
    (∀ w : ℕ → h04 L 3, Tendsto (fun k => m31 (w k)) atTop (𝓝 u0) → ∀ T : ℝ,
      TendstoUniformlyOn (fun k t => m31 (umax hs3 κ (w k) t)) (umax (le_refl (1 : ℝ)) κ u0)
        atTop (Set.Icc (-T) T)) := by
  have hu := umax1_mild hκ u0
  have hmem : ∀ t : ℝ, t ∈ Imax (le_refl (1 : ℝ)) κ u0 := fun t => by
    rw [Imax1_eq_univ hκ u0]; trivial
  have hcont : Continuous (umax (le_refl (1 : ℝ)) κ u0) := continuousOn_univ.mp hu.cont
  have hC := mild_C1 hu
  have hder : ∀ t, HasDerivAt (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t))
      (Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t)) t := fun t =>
    hC.2.2.2.1 t (by rw [interior_univ]; trivial)
  refine ⟨hu, hcont, ?_, hder, fun t => hC.2.2.2.2 t (Set.mem_univ t), fun v hv hv0 t => ?_,
    fun J v hv t ht => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun N => ?_,
    fun T => approx hκ (PN_tendsto u0) T, fun w hw T => approx hκ hw T⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hder t).differentiableAt, ?_⟩
    have e : deriv (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t)) =
        fun t => Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t) :=
      funext fun t => (hder t).deriv
    rw [e]
    exact (continuous_Gder (le_refl (1 : ℝ)) κ).comp hcont
  · have hv' := dist_isMild hv (Set.mem_univ 0)
    rw [hv0] at hv'
    exact mild_unique (le_refl (1 : ℝ)) hκ hv' hu t (Set.mem_univ t)
  · exact mild_unique (le_refl (1 : ℝ)) hκ hv (hu.mono (Set.subset_univ J) hv.zero_mem
      hv.ordConnected) t ht
  · rw [← mass_eq_integral, ← mass_eq_integral, mass_cons1 hκ u0 (hmem t)]
  · rw [← energy_eq_energyH1, ← energy_eq_energyH1, energy_cons1 hκ u0 (hmem t)]
  · rw [← mass_eq_integral, ← energy_eq_energyH1]
    exact bound1 hκ u0 (hmem t)
  · exact ⟨(lem_regular hκ (PN N u0)).2.2.1, (lem_regular hκ (PN N u0)).2.2.2.1⟩

#print axioms thm_global

end Flow

end QuantumNLS.F04Global
