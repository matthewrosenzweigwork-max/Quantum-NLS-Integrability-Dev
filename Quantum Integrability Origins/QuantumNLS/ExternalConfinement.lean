import QuantumNLS.GaudinResponse

/-!
# CC:F04:external-confinement (R-52E511D4): confinement with a monotone external force

Source: `source/chapters/root_response/F04.tex`, Lemma `CC:F04:external-confinement` (lines 36-52)
and its proof (lines 53-93); standing assumption `L > 0` (line 3, "Fix `L, κ > 0`").

Statement: let `K ≥ 1`, `c > 0`, `H : ℝ → ℝ` continuous with `H(y) − H(x) ≥ L(y − x)` for `y ≥ x`.
If `t_1 < ⋯ < t_K` and `ν_1 ≤ ⋯ ≤ ν_K` obey
`H(t_i) − 2 Σ_{j≠i} arctan (c/(t_i − t_j)) = 2πν_i` (`CC:F04:external-equations`), then `H` is onto
and, with `p_i = H^{-1}(2πν_i)`, `|t_i − p_i| ≤ 4√(cK/L)` (`CC:F04:external-bound`).

Lean indices are zero based (`Fin K`); the labels `ν_i` are real numbers.

Route (as printed): surjectivity from the lower slope; the order comparison at an index of
`max (x_i − y_i)` (`comparison`), applied to the prefix `{j ≤ i}` and the suffix `{j ≥ i}` of the
actual array, compared with the shifted all-zero-label ground array of the same size, whose bound
`|s_j| ≤ 2√(cm/L)` is the accepted R-39906D9E (`GaudinResponse.ground_roots_symmetric`).

Recorded deviations (none changes the statement):
* The comparison is proved directly for the Bose left sides on a sub-array (index set `S`): for two
  arrays strictly ordered on `S`, `arctan(c/d) = (π/2) sgn d − arctan(d/c)` and the signs agree, so
  the printed passage through `T_H` and the fixed chamber vector `π(2i−K−1)` is done termwise.
* Sub-arrays are index subsets `S ⊆ Fin K` (`Finset.Iic i`, `Finset.Ici i`); the ground array of
  size `#S` is transported along `Finset.orderIsoOfFin`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Filter

namespace QuantumNLS.ExternalConfinement

/-- The Bose left side of `CC:F04:external-equations` restricted to the coordinates in `S`. -/
def boseS {ι : Type*} [DecidableEq ι] (H : ℝ → ℝ) (c : ℝ) (S : Finset ι) (x : ι → ℝ) (j : ι) : ℝ :=
  H (x j) - 2 * ∑ k ∈ S.erase j, Real.arctan (c / (x j - x k))

/-- `arctan (c/d) − arctan (c/e) = arctan (e/c) − arctan (d/c)` when `d, e` have the same sign. -/
lemma arctan_same_sign {c d e : ℝ} (hc : 0 < c) (hd : d ≠ 0) (he : e ≠ 0)
    (hs : Real.sign d = Real.sign e) :
    Real.arctan (c / d) - Real.arctan (c / e) = Real.arctan (e / c) - Real.arctan (d / c) := by
  have h1 := RootContraction.arctan_div_add_arctan_div hc hd
  have h2 := RootContraction.arctan_div_add_arctan_div hc he
  rw [hs] at h1
  linarith

/-- **Order comparison** (printed first paragraph of the proof) on an index set `S`: if `x, y` are
strictly ordered on `S` and the Bose left sides satisfy `boseS x ≤ boseS y` on `S`, then `x ≤ y`
on `S`. -/
theorem comparison {ι : Type*} [LinearOrder ι] {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {H : ℝ → ℝ}
    (hH : ∀ x y, x ≤ y → L * (y - x) ≤ H y - H x) {S : Finset ι} {x y : ι → ℝ}
    (hx : StrictMonoOn x S) (hy : StrictMonoOn y S)
    (h : ∀ j ∈ S, boseS H c S x j ≤ boseS H c S y j) : ∀ j ∈ S, x j ≤ y j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, hj0S, hj0⟩ := hcon
  obtain ⟨k, hkS, hkmax⟩ := S.exists_max_image (fun j => x j - y j) ⟨j0, hj0S⟩
  have hd : 0 < x k - y k := by have := hkmax j0 hj0S; linarith
  have hHk : L * (x k - y k) ≤ H (x k) - H (y k) := hH (y k) (x k) (by linarith)
  have hterm : ∀ l ∈ S.erase k,
      Real.arctan (c / (x k - x l)) - Real.arctan (c / (y k - y l)) ≤ 0 := by
    intro l hl
    have hlS := Finset.mem_of_mem_erase hl
    have hlk := Finset.ne_of_mem_erase hl
    have hmono : y k - y l ≤ x k - x l := by have := hkmax l hlS; linarith
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · have h1 : 0 < x k - x l := sub_pos.mpr (hx hlS hkS hlt)
      have h2 : 0 < y k - y l := sub_pos.mpr (hy hlS hkS hlt)
      rw [arctan_same_sign hc h1.ne' h2.ne' (by rw [Real.sign_of_pos h1, Real.sign_of_pos h2])]
      have := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right hmono hc.le)
      linarith
    · have h1 : x k - x l < 0 := sub_neg.mpr (hx hkS hlS hgt)
      have h2 : y k - y l < 0 := sub_neg.mpr (hy hkS hlS hgt)
      rw [arctan_same_sign hc h1.ne h2.ne (by rw [Real.sign_of_neg h1, Real.sign_of_neg h2])]
      have := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right hmono hc.le)
      linarith
  have hsum : ∑ l ∈ S.erase k, Real.arctan (c / (x k - x l)) ≤
      ∑ l ∈ S.erase k, Real.arctan (c / (y k - y l)) :=
    Finset.sum_le_sum fun l hl => by linarith [hterm l hl]
  have := h k hkS
  unfold boseS at this
  nlinarith

/-! ## Surjectivity of `H` -/

theorem H_surjective {L : ℝ} (hL : 0 < L) {H : ℝ → ℝ} (hHc : Continuous H)
    (hH : ∀ x y, x ≤ y → L * (y - x) ≤ H y - H x) : Function.Surjective H := by
  refine hHc.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_left atTop (H 0)
      (tendsto_id.const_mul_atTop hL))
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := hH 0 x hx
    simp only [id]; linarith
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_left atBot (H 0)
      (tendsto_id.const_mul_atBot hL))
    filter_upwards [eventually_le_atBot 0] with x hx
    have := hH x 0 hx
    simp only [id]; linarith

theorem H_injective {L : ℝ} (hL : 0 < L) {H : ℝ → ℝ}
    (hH : ∀ x y, x ≤ y → L * (y - x) ≤ H y - H x) : Function.Injective H := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hH a b h.le; rw [hab] at this; nlinarith
  · have := hH b a h.le; rw [hab] at this; nlinarith

/-! ## Transport of the ground array to an index set -/

/-- Reindexing a sum over `S.erase (e a)` along `e : Fin m ≃o S`. -/
lemma sum_erase_transport {K m : ℕ} {S : Finset (Fin K)} (e : Fin m ≃o S) (F : Fin K → ℝ)
    (a : Fin m) :
    ∑ k ∈ S.erase (e a), F k = ∑ b ∈ univ.erase a, F (e b) := by
  symm
  refine Finset.sum_bij (fun b _ => (e b : Fin K)) (fun b hb => ?_) (fun b1 _ b2 _ h => ?_)
    (fun k hk => ?_) (fun b _ => rfl)
  · refine Finset.mem_erase.mpr ⟨fun h => ?_, (e b).2⟩
    exact (Finset.ne_of_mem_erase hb) (e.injective (Subtype.ext h))
  · exact e.injective (Subtype.ext h)
  · have hkS := Finset.mem_of_mem_erase hk
    refine ⟨e.symm ⟨k, hkS⟩, Finset.mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩, by simp⟩
    apply Finset.ne_of_mem_erase hk
    rw [← h]; simp

/-- The shifted ground array on `S`: `y_{e(a)} = p + δ + s_a` with `s` the all-zero-label ground
roots of size `m = #S`. -/
def shiftedGround {K m : ℕ} {S : Finset (Fin K)} (e : Fin m ≃o S) (L c v : ℝ) (k : Fin K) : ℝ :=
  if h : k ∈ S then v + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c (e.symm ⟨k, h⟩) else 0

lemma shiftedGround_apply {K m : ℕ} {S : Finset (Fin K)} (e : Fin m ≃o S) (L c v : ℝ) (a : Fin m) :
    shiftedGround e L c v (e a) = v + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
  unfold shiftedGround
  simp

lemma shiftedGround_strictMonoOn {K m : ℕ} {S : Finset (Fin K)} (e : Fin m ≃o S) {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) (v : ℝ) : StrictMonoOn (shiftedGround e L c v) S := by
  intro k1 h1 k2 h2 hlt
  have hs := (RootContraction.isActual_roots (N := m) hL hc (n := fun _ => 0)
    (fun _ _ _ => le_rfl)).sorted
  have h1' : k1 ∈ S := Finset.mem_coe.mp h1
  have h2' : k2 ∈ S := Finset.mem_coe.mp h2
  unfold shiftedGround
  simp only [h1', h2', ↓reduceDIte]
  have : e.symm ⟨k1, h1'⟩ < e.symm ⟨k2, h2'⟩ := e.symm.strictMono (Subtype.mk_lt_mk.mpr hlt)
  linarith [hs this]

/-- The Bose left side of the shifted ground array with the linear force: `boseS = H(y) − L s`. -/
lemma boseS_shiftedGround {K m : ℕ} {S : Finset (Fin K)} (e : Fin m ≃o S) {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) (H : ℝ → ℝ) (v : ℝ) (a : Fin m) :
    boseS H c S (shiftedGround e L c v) (e a) =
      H (shiftedGround e L c v (e a)) - L * BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
  have ha := (RootContraction.isActual_roots (N := m) hL hc (n := fun _ => 0)
    (fun _ _ _ => le_rfl)).bethe a
  unfold boseS
  rw [sum_erase_transport e]
  simp only [shiftedGround_apply, add_sub_add_left_eq_sub]
  simp only [Int.cast_zero, mul_zero, zero_add] at ha
  linarith

/-! ## The lemma -/

/-- **CC:F04:external-confinement** (R-52E511D4). -/
theorem external_confinement {K : ℕ} (_hK : 1 ≤ K) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {H : ℝ → ℝ} (hHc : Continuous H) (hH : ∀ x y, x ≤ y → L * (y - x) ≤ H y - H x)
    {t ν : Fin K → ℝ} (ht : StrictMono t) (hν : Monotone ν)
    (heq : ∀ i, H (t i) - 2 * ∑ j ∈ univ.erase i, Real.arctan (c / (t i - t j)) =
      2 * Real.pi * ν i) :
    Function.Surjective H ∧ Function.Injective H ∧
      ∀ i (p : ℝ), H p = 2 * Real.pi * ν i → |t i - p| ≤ 4 * Real.sqrt (c * K / L) := by
  refine ⟨H_surjective hL hHc hH, H_injective hL hH, fun i p hp => ?_⟩
  -- Bose left sides of the actual array on a sub-array
  have hsplit : ∀ (S : Finset (Fin K)) j, j ∈ S →
      boseS H c S t j = 2 * Real.pi * ν j +
        2 * ∑ k ∈ univ.filter (fun k => k ∉ S), Real.arctan (c / (t j - t k)) := by
    intro S j hj
    have e1 : ∑ k ∈ univ.erase j, Real.arctan (c / (t j - t k)) =
        ∑ k ∈ S.erase j, Real.arctan (c / (t j - t k)) +
          ∑ k ∈ univ.filter (fun k => k ∉ S), Real.arctan (c / (t j - t k)) := by
      rw [← Finset.sum_filter_add_sum_filter_not (univ.erase j) (fun k => k ∈ S)]
      congr 1
      · congr 1; ext k; simp [and_comm]
      · congr 1; ext k; simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
        exact ⟨fun h => h.2, fun h => ⟨fun hk => h (hk ▸ hj), h⟩⟩
    have := heq j
    unfold boseS
    linarith
  have hm1 : ∀ S : Finset (Fin K), i ∈ S → 1 ≤ S.card := fun S hS => Finset.card_pos.mpr ⟨i, hS⟩
  have hR : ∀ m : ℕ, m ≤ K → 2 * Real.sqrt (c * m / L) ≤ 2 * Real.sqrt (c * K / L) := by
    intro m hm
    have : (m : ℝ) ≤ K := by exact_mod_cast hm
    gcongr
  have ground := fun (m : ℕ) (hm : 1 ≤ m) =>
    GaudinResponse.ground_roots_symmetric (N := m) hL hc hm
  rw [abs_le]
  constructor
  · -- suffix: `p − 4√(cK/L) ≤ t_i`
    set S := Finset.Ici i
    set m := S.card
    have hiS : i ∈ S := Finset.mem_Ici.mpr le_rfl
    set e := S.orderIsoOfFin (k := m) rfl
    have hgr := (ground m (hm1 S hiS)).2
    have hRK := hR m (le_trans (Finset.card_le_univ S) (by simp))
    set y := shiftedGround e L c (p - 2 * Real.sqrt (c * m / L))
    have hcmp := comparison hL hc hH (S := S) (x := y) (y := t)
      (shiftedGround_strictMonoOn e hL hc _) (ht.strictMonoOn _) (fun j hj => ?_)
    · have hti := hcmp i hiS
      obtain ⟨a, ha⟩ : ∃ a, e a = ⟨i, hiS⟩ := e.surjective _
      have hya : y i = p - 2 * Real.sqrt (c * m / L) + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
        have := shiftedGround_apply e L c (p - 2 * Real.sqrt (c * m / L)) a
        rw [ha] at this; exact this
      have := hgr a
      rw [abs_le] at this
      linarith
    · have h1 : 2 * Real.pi * ν i ≤ boseS H c S t j := by
        rw [hsplit S j hj]
        have hij : i ≤ j := Finset.mem_Ici.mp hj
        have hpos : 0 ≤ ∑ k ∈ univ.filter (fun k => k ∉ S), Real.arctan (c / (t j - t k)) := by
          refine Finset.sum_nonneg fun k hk => ?_
          have hk' : k < i := by
            have := (Finset.mem_filter.mp hk).2; rw [Finset.mem_Ici] at this; exact not_le.mp this
          have : 0 < t j - t k := sub_pos.mpr (ht (lt_of_lt_of_le hk' hij))
          exact (Real.arctan_pos.mpr (div_pos hc this)).le
        have := hν hij
        nlinarith [Real.pi_pos]
      obtain ⟨a, ha⟩ : ∃ a, e a = ⟨j, hj⟩ := e.surjective _
      have hb := boseS_shiftedGround e hL hc H (p - 2 * Real.sqrt (c * m / L)) a
      rw [ha] at hb
      simp only at hb
      rw [hb]
      have hsa := hgr a
      rw [abs_le] at hsa
      have hy : y j = p - 2 * Real.sqrt (c * m / L) + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
        have := shiftedGround_apply e L c (p - 2 * Real.sqrt (c * m / L)) a
        rw [ha] at this; exact this
      have hHy := hH (y j) p (by rw [hy]; linarith)
      have hR0 : 0 ≤ 2 * Real.sqrt (c * m / L) := by have := Real.sqrt_nonneg (c * m / L); linarith
      rw [show shiftedGround e L c (p - 2 * Real.sqrt (c * m / L)) j = y j from rfl]
      nlinarith

  · -- prefix: `t_i ≤ p + 4√(cK/L)`
    set S := Finset.Iic i
    set m := S.card
    have hiS : i ∈ S := Finset.mem_Iic.mpr le_rfl
    set e := S.orderIsoOfFin (k := m) rfl
    have hgr := (ground m (hm1 S hiS)).2
    have hRK := hR m (le_trans (Finset.card_le_univ S) (by simp))
    set y := shiftedGround e L c (p + 2 * Real.sqrt (c * m / L))
    have hcmp := comparison hL hc hH (S := S) (x := t) (y := y) (ht.strictMonoOn _)
      (shiftedGround_strictMonoOn e hL hc _) (fun j hj => ?_)
    · have hti := hcmp i hiS
      obtain ⟨a, ha⟩ : ∃ a, e a = ⟨i, hiS⟩ := e.surjective _
      have hya : y i = p + 2 * Real.sqrt (c * m / L) + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
        have := shiftedGround_apply e L c (p + 2 * Real.sqrt (c * m / L)) a
        rw [ha] at this; exact this
      have := hgr a
      rw [abs_le] at this
      linarith
    · -- the actual prefix left sides are at most `2πν_i ≤` those of `y`
      have h1 : boseS H c S t j ≤ 2 * Real.pi * ν i := by
        rw [hsplit S j hj]
        have hji : j ≤ i := Finset.mem_Iic.mp hj
        have hneg : ∑ k ∈ univ.filter (fun k => k ∉ S), Real.arctan (c / (t j - t k)) ≤ 0 := by
          refine Finset.sum_nonpos fun k hk => ?_
          have hk' : i < k := by
            have := (Finset.mem_filter.mp hk).2; rw [Finset.mem_Iic] at this; exact not_le.mp this
          have : t j - t k < 0 := sub_neg.mpr (ht (lt_of_le_of_lt hji hk'))
          exact (Real.arctan_lt_zero.mpr (div_neg_of_pos_of_neg hc this)).le
        have := hν hji
        nlinarith [Real.pi_pos]
      obtain ⟨a, ha⟩ : ∃ a, e a = ⟨j, hj⟩ := e.surjective _
      have hb := boseS_shiftedGround e hL hc H (p + 2 * Real.sqrt (c * m / L)) a
      rw [ha] at hb
      simp only at hb
      rw [hb]
      have hsa := hgr a
      rw [abs_le] at hsa
      have hy : y j = p + 2 * Real.sqrt (c * m / L) + BetheSmooth.roots L (fun _ : Fin m => (0 : ℤ)) c a := by
        have := shiftedGround_apply e L c (p + 2 * Real.sqrt (c * m / L)) a
        rw [ha] at this; exact this
      have hHy := hH p (y j) (by rw [hy]; linarith)
      have hR0 : 0 ≤ 2 * Real.sqrt (c * m / L) := by have := Real.sqrt_nonneg (c * m / L); linarith
      rw [show shiftedGround e L c (p + 2 * Real.sqrt (c * m / L)) j = y j from rfl]
      nlinarith

/-- The same bound with `p_i = H^{-1}(2πν_i)` written through the inverse of the bijection `H`. -/
theorem external_confinement_inv {K : ℕ} (hK : 1 ≤ K) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {H : ℝ → ℝ} (hHc : Continuous H) (hH : ∀ x y, x ≤ y → L * (y - x) ≤ H y - H x)
    {t ν : Fin K → ℝ} (ht : StrictMono t) (hν : Monotone ν)
    (heq : ∀ i, H (t i) - 2 * ∑ j ∈ univ.erase i, Real.arctan (c / (t i - t j)) =
      2 * Real.pi * ν i) (i : Fin K) :
    |t i - Function.surjInv (H_surjective hL hHc hH) (2 * Real.pi * ν i)| ≤
      4 * Real.sqrt (c * K / L) :=
  (external_confinement hK hL hc hHc hH ht hν heq).2.2 i _
    (Function.surjInv_eq (H_surjective hL hHc hH) _)

/-! Kernel axiom audit (checkpoint EC1). -/
#print axioms arctan_same_sign
#print axioms comparison
#print axioms H_surjective
#print axioms H_injective
#print axioms sum_erase_transport
#print axioms shiftedGround_apply
#print axioms shiftedGround_strictMonoOn
#print axioms boseS_shiftedGround
#print axioms external_confinement
#print axioms external_confinement_inv

end QuantumNLS.ExternalConfinement
