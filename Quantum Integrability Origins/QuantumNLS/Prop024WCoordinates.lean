import QuantumNLS.Ext006SeriesIdentificationR43a

/-! PROP-024 affine Weyl action, module 1 (occupation coordinates).

Foundational coordinate-level facts used by the affine Weyl action
`W(v)* a(f) W(v) = a(f) + <f,v>` on the actual occupation Fock space
(`Ext006VacuumRecurrence.Fock = L2 Occ`) of the frozen EXT-006 chain.

* the coordinate functionals `y ↦ (a(g) y)_m` and `y ↦ (a*(g) y)_m` are bounded linear
  functionals on all of `Fock` (no smoothness of `y` is used), and they agree with the
  frozen smooth-domain operators `A g`, `C g` on `D`;
* weighted number energies `En p y = ∑_m (total m + 1)^p ‖y m‖²` in `[0,∞]`, with the exact
  characterization of the common smooth domain `Smooth y ↔ ∀ p, En p y ≠ ∞`;
* the exact annihilation Fubini identity
  `∑_a En p (a_a y) = ∑_m (total m)^(p+1) ‖y m‖²` valid for EVERY `y : Fock` (in `[0,∞]`);
* finite-particle truncations converge in `Fock` and tails of summable families vanish.

Nothing here is a Weyl/interaction compatibility premise; all objects are the frozen
`Ext006` ones.  No sorry, no new axiom. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal Topology
open Filter
namespace QuantumNLS.Prop024WCoordinates
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006SmoothOperatorsR34a
open Ext006FieldBoundsR42a

/-! ### Bounded coordinate functionals -/

lemma norm_xvec_le (w : Fock) (m : Occ) :
    ‖xvec w m‖ ≤ Real.sqrt ((total m : ℝ)+1) * ‖w‖ := by
  have hinj : Function.Injective (fun c : ℤ => m + e c) := by
    intro a b hab
    have := add_left_cancel hab
    exact (Finsupp.single_left_injective one_ne_zero) this
  have hs := (summable_sq w).comp_injective hinj
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) (xvec w m)
  have h2 := lp.hasSum_norm (p := 2) (by norm_num) w
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
  have hsq : ‖xvec w m‖^2 ≤ ((total m : ℝ)+1) * ‖w‖^2 := by
    rw [← h1.tsum_eq, ← h2.tsum_eq]
    calc
      ∑' c : ℤ, ‖xvec w m c‖^2 ≤ ∑' c : ℤ, (((total m : ℝ)+1) * ‖w (m + e c)‖^2) := by
        refine Summable.tsum_le_tsum (fun c => ?_) h1.summable (hs.mul_left _)
        change ‖xcoord w m c‖^2 ≤ _
        simp only [xcoord]
        rw [norm_sq_sqrt_mul _ (by positivity)]
        have := n_le_total m c
        have h3 : ((m c : ℝ)+1) ≤ (total m : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ this
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = ((total m : ℝ)+1) * ∑' c : ℤ, ‖w (m + e c)‖^2 := tsum_mul_left
      _ ≤ ((total m : ℝ)+1) * ∑' b : Occ, ‖w b‖^2 :=
        mul_le_mul_of_nonneg_left
          (tsum_comp_le_tsum_of_inj (f := fun b : Occ => ‖w b‖^2) (summable_sq w)
            (fun _ => sq_nonneg _) hinj) (by positivity)
  have h0 : 0 ≤ Real.sqrt ((total m : ℝ)+1) * ‖w‖ := by positivity
  have hmul : (Real.sqrt ((total m : ℝ)+1) * ‖w‖)^2 = ((total m : ℝ)+1) * ‖w‖^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact abs_le_of_sq_le_sq' (by rw [hmul]; exact hsq) h0 |>.2

/-- The occupation-`m` coordinate map `y ↦ xvec y m`, as a bounded linear map into `ℓ²(ℤ)`. -/
def xvecCLM (m : Occ) : Fock →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun w => xvec w m
      map_add' := fun v w => xvec_add v w m
      map_smul' := fun c w => xvec_smul c w m }
    (Real.sqrt ((total m : ℝ)+1)) (norm_xvec_le · m)

lemma xvecCLM_apply (m : Occ) (w : Fock) : xvecCLM m w = xvec w m := rfl

/-- Annihilation coordinate functional: `(a(g) y)_m = ⟨g, xvec y m⟩`, bounded on all of `Fock`. -/
def annC (g : H) (m : Occ) : Fock →L[ℂ] ℂ := (innerSL ℂ g).comp (xvecCLM m)

lemma annC_apply (g : H) (m : Occ) (w : Fock) : annC g m w = inner ℂ g (xvec w m) := rfl

/-- Creation coordinate functional: a finite sum of coordinate evaluations. -/
def creC (g : H) (m : Occ) : Fock →L[ℂ] ℂ :=
  ∑ a ∈ m.support, (g a * (Real.sqrt (m a : ℝ) : ℂ)) •
    (lp.evalCLM ℂ (fun _ : Occ => ℂ) 2 (m - e a))

lemma creC_apply (g : H) (m : Occ) (w : Fock) :
    creC g m w = ∑ a ∈ m.support, g a * creCoeff a w m := by
  simp only [creC, sum_apply, smul_apply,
    lp.evalCLM, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [creCoeff]
  change (g a * (Real.sqrt (m a : ℝ) : ℂ)) * (lp.evalₗ (fun _ : Occ => ℂ) 2 (m - e a) : Fock →ₗ[ℂ] ℂ) w = _
  simp only [lp.evalₗ_apply]
  ring

/-- The frozen smooth-domain annihilator is the coordinate functional. -/
lemma A_coord (g : H) (w : D) (m : Occ) : (A g w).1 m = annC g m w.1 := rfl

/-- The frozen smooth-domain creator is the coordinate functional. -/
lemma C_coord (g : H) (w : D) (m : Occ) : (C g w).1 m = creC g m w.1 := by
  rw [creC_apply]
  rfl

/-- Mode-`a` annihilation coordinate is the explicit formula. -/
lemma annC_single (a : ℤ) (m : Occ) (w : Fock) :
    annC (lp.single 2 a (1 : ℂ)) m w = xcoord w m a := by
  rw [annC_apply, lp.inner_single_left]
  simp [xvec_apply]

/-! ### Number energies and the smooth domain -/

/-- The polynomial number weight. -/
def wt (p : ℕ) (m : Occ) : ℝ := ((total m : ℝ)+1)^p

lemma wt_nonneg (p : ℕ) (m : Occ) : 0 ≤ wt p m := by unfold wt; positivity

/-- Weighted number energy in `[0,∞]`. -/
def En (p : ℕ) (y : Occ → ℂ) : ℝ≥0∞ := ∑' m : Occ, ENNReal.ofReal (wt p m * ‖y m‖^2)

lemma smooth_iff_En (y : Occ → ℂ) : Smooth y ↔ ∀ p, En p y ≠ ⊤ := by
  constructor
  · intro h p
    have hs := h p
    have := ENNReal.ofReal_tsum_of_nonneg
      (f := fun m => wt p m * ‖y m‖^2) (fun m => mul_nonneg (wt_nonneg p m) (sq_nonneg _)) hs
    unfold En
    rw [← this]
    exact ENNReal.ofReal_ne_top
  · intro h p
    have hs := ENNReal.summable_toReal (h p)
    refine hs.congr fun m => ?_
    exact ENNReal.toReal_ofReal (mul_nonneg (wt_nonneg p m) (sq_nonneg _))

lemma En_mono {p q : ℕ} (hpq : p ≤ q) (y : Occ → ℂ) : En p y ≤ En q y := by
  refine ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) (total m); linarith) hpq

lemma En_zero (y : Fock) : En 0 y = ENNReal.ofReal (‖y‖^2) := by
  have h2 := lp.hasSum_norm (p := 2) (by norm_num) y
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  rw [← h2.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h2.summable]
  simp [En, wt]

lemma norm_sq_le_En (p : ℕ) (y : Fock) : ENNReal.ofReal (‖y‖^2) ≤ En p y := by
  rw [← En_zero]
  exact En_mono (Nat.zero_le p) y

lemma En_add_le (p : ℕ) (u v : Occ → ℂ) :
    En p (u + v) ≤ 2 * En p u + 2 * En p v := by
  unfold En
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun m => ?_
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg (wt_nonneg p m) (sq_nonneg _)))
      (mul_nonneg (by norm_num) (mul_nonneg (wt_nonneg p m) (sq_nonneg _)))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : ‖u m + v m‖^2 ≤ 2 * ‖u m‖^2 + 2 * ‖v m‖^2 := by
    have h := norm_add_le (u m) (v m)
    nlinarith [sq_nonneg (‖u m‖ - ‖v m‖), norm_nonneg (u m), norm_nonneg (v m),
      norm_nonneg (u m + v m)]
  have hw := wt_nonneg p m
  simp only [Pi.add_apply]
  nlinarith

lemma En_smul (p : ℕ) (c : ℂ) (u : Occ → ℂ) :
    En p (c • u) = ENNReal.ofReal (‖c‖^2) * En p u := by
  unfold En
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  simp only [Pi.smul_apply, norm_smul, mul_pow]
  ring

lemma En_le_of_norm_le (p : ℕ) {u v : Occ → ℂ} (h : ∀ m, ‖u m‖ ≤ ‖v m‖) : En p u ≤ En p v := by
  refine ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h m) 2) (wt_nonneg p m)

/-! ### The exact annihilation Fubini identity, valid for every `y : Fock` -/

lemma total_eq_tsum' (m : Occ) : (total m : ℝ≥0∞) = ∑' d : ℤ, (m d : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := m.support) (fun d hd => by
    rw [Finsupp.notMem_support_iff.mp hd]; simp)]
  simp only [total, Finsupp.degree_apply, Nat.cast_sum]

theorem ann_energy_sum (p : ℕ) (y : Fock) :
    ∑' a : ℤ, En p (fun m => xcoord y m a) =
      ∑' m : Occ, ENNReal.ofReal (((total m : ℝ))^(p+1) * ‖y m‖^2) := by
  let F : Occ → ℤ → ℝ≥0∞ := fun m a =>
    ENNReal.ofReal (((total m : ℝ))^p * ‖y m‖^2) * (m a : ℝ≥0∞)
  have hterm (m : Occ) (a : ℤ) :
      ENNReal.ofReal (wt p m * ‖xcoord y m a‖^2) = F (m + e a) a := by
    simp only [F, xcoord, wt]
    rw [norm_sq_sqrt_mul _ (by positivity)]
    have h1 : ((total (m + e a) : ℕ) : ℝ) = (total m : ℝ) + 1 := by
      rw [total_add_e]; push_cast; ring
    have h2 : (((m + e a) a : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m a : ℝ) + 1) := by
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    rw [h2, h1, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    ∑' a : ℤ, En p (fun m => xcoord y m a)
        = ∑' a : ℤ, ∑' m : Occ, F (m + e a) a := by
          refine tsum_congr fun a => tsum_congr fun m => ?_
          exact hterm m a
    _ = ∑' m : Occ, ∑' a : ℤ, F (m + e a) a := ENNReal.tsum_comm
    _ = ∑' z : Occ × ℤ, F (z.1 + e z.2) z.2 := ENNReal.tsum_prod.symm
    _ = ∑' z : Occ × ℤ, F z.1 z.2 := by
          refine shift_pair_injective.tsum_eq (f := fun z : Occ × ℤ => F z.1 z.2) ?_
          intro z hz
          by_contra hn
          apply hz
          have hm : z.1 z.2 = 0 := by
            by_contra hne
            exact hn ⟨(z.1 - e z.2, z.2), Prod.ext (shift_sub_add (Nat.one_le_iff_ne_zero.mpr hne)) rfl⟩
          simp [F, hm]
    _ = ∑' m : Occ, ∑' a : ℤ, F m a := ENNReal.tsum_prod
    _ = ∑' m : Occ, ENNReal.ofReal (((total m : ℝ))^(p+1) * ‖y m‖^2) := by
          refine tsum_congr fun m => ?_
          simp only [F]
          rw [ENNReal.tsum_mul_left, ← total_eq_tsum']
          rw [show ((total m : ℕ) : ℝ≥0∞) = ENNReal.ofReal (total m : ℝ) by simp,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring

/-! ### Truncations and tails -/

/-- The finite-particle truncation `1_{total ≤ K} y`. -/
def truncFock (K : ℕ) (x : Fock) : Fock :=
  ⟨fun m => if total m ≤ K then x m else 0, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (summable_sq x)
    by_cases h : total m ≤ K <;> simp [h]⟩

lemma truncFock_apply (K : ℕ) (x : Fock) (m : Occ) :
    truncFock K x m = if total m ≤ K then x m else 0 := rfl

lemma truncFock_particleBound (K : ℕ) (x : Fock) : ParticleBound K (truncFock K x) := by
  intro m hm
  rw [truncFock_apply, if_neg (by omega)]

lemma truncFock_smooth (K : ℕ) (x : Fock) : Smooth (truncFock K x) := by
  intro p
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((summable_sq x).mul_left (((K : ℝ)+1)^p))
  rw [truncFock_apply]
  by_cases h : total m ≤ K
  · rw [if_pos h]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ h) p) (sq_nonneg _)
  · rw [if_neg h]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity

lemma tail_tendsto (f : Occ → ℝ) (hf : Summable f) (hnn : ∀ m, 0 ≤ f m) :
    Tendsto (fun K : ℕ => ∑' m : Occ, (if K < total m then f m else 0)) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (K : ℕ) (m : Occ) => if K < total m then f m else 0) (g := fun _ => (0 : ℝ))
    (bound := f) hf ?_ ?_
  · simpa using this
  · intro m
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (total m)] with K hK
    simp [not_lt.mpr hK]
  · refine Eventually.of_forall fun K m => ?_
    by_cases h : K < total m
    · simp [h, abs_of_nonneg (hnn m)]
    · simp [h, hnn m]

lemma norm_sq_sub_truncFock (K : ℕ) (x : Fock) :
    ‖x - truncFock K x‖^2 = ∑' m : Occ, (if K < total m then ‖x m‖^2 else 0) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (x - truncFock K x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← h.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, truncFock_apply]
  by_cases hm : total m ≤ K
  · simp [hm, not_lt.mpr hm]
  · simp [hm, not_le.mp hm]

lemma tendsto_truncFock (x : Fock) : Tendsto (fun K : ℕ => truncFock K x) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tail_tendsto (fun m => ‖x m‖^2) (summable_sq x) (fun m => sq_nonneg _)
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  refine h2.congr (fun K => ?_)
  simp only [Function.comp_apply]
  rw [← norm_sq_sub_truncFock, Real.sqrt_sq (norm_nonneg _), norm_sub_rev]

end QuantumNLS.Prop024WCoordinates

#print axioms QuantumNLS.Prop024WCoordinates.norm_xvec_le
#print axioms QuantumNLS.Prop024WCoordinates.creC_apply
#print axioms QuantumNLS.Prop024WCoordinates.smooth_iff_En
#print axioms QuantumNLS.Prop024WCoordinates.ann_energy_sum
#print axioms QuantumNLS.Prop024WCoordinates.tendsto_truncFock

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WCoordinates." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WCoordinates." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop024WCoordinates aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
