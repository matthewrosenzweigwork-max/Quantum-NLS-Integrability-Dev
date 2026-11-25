import QuantumNLS.Prop024WCoreAffine

/-! PROP-024 affine Weyl action, module 3: the displacement preserves every number-moment
domain, with an a priori bound.

For the frozen EXT-006 unitary `U = unitary h t` (so `U = exp(i t (a*(h)+a(h)))`) and every
`p : ℕ`, `y ∈ ℓ²(Occ)`:

  `En p (U y) ≤ Cn p · En p y`   in `[0,∞]`,

with `Cn` an explicit finite constant depending only on `p` and `t²‖h‖²`.  Hence `U` maps each
polynomial number-moment domain `{En p < ∞}` and the common smooth domain
`Smooth = ⋂ₚ {En p < ∞}` into themselves.

Proof: induction on `p`.  On finite-particle vectors the step uses the affine identity of
module 2 together with the exact annihilation Fubini identity of module 1
(`∑_a En p (a_a y) = ∑_m (total m)^(p+1) ‖y m‖²`); general vectors are reached by the
`1_{total ≤ K}` truncations and lower semicontinuity of the energies on finite coordinate
sets.  No compatibility premise is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal Topology
open Filter
namespace QuantumNLS.Prop024WEnergy
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmoothOperatorsR34a Ext006FieldBoundsR42a Ext006StrongFieldR41a
open Ext006BoundedExponentialR43a Prop024WCoordinates Prop024WCoreAffine

/-- The explicit energy-growth constants. -/
def Cn (B : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 1
  | p+1 => 2^(p+2) * Cn B p * (1 + B) + 1

lemma Cn_ne_top {B : ℝ≥0∞} (hB : B ≠ ⊤) : ∀ p, Cn B p ≠ ⊤
  | 0 => ENNReal.one_ne_top
  | p+1 => by
    have ih := Cn_ne_top hB p
    unfold Cn
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ih)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hB⟩), ENNReal.one_ne_top⟩

lemma succ_pow_le (n p : ℕ) :
    ((n : ℝ)+1)^(p+1) ≤ 2^(p+1) * (n : ℝ)^(p+1) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n : ℝ)+1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc
      ((n : ℝ)+1)^(p+1) ≤ (2 * (n : ℝ))^(p+1) :=
        pow_le_pow_left₀ (by positivity) h1 _
      _ = 2^(p+1) * (n : ℝ)^(p+1) := mul_pow _ _ _
      _ ≤ _ := by linarith

/-- One step up in the energy scale, controlled by annihilation energies. -/
lemma En_succ_le (p : ℕ) (y : Fock) :
    En (p+1) y ≤ 2^(p+1) * (∑' a : ℤ, En p (fun m => xcoord y m a)) +
      ENNReal.ofReal (‖y‖^2) := by
  rw [ann_energy_sum, ← En_zero y]
  have h2 : ((2 : ℝ≥0∞)^(p+1)) = ENNReal.ofReal (2^(p+1)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, ← ENNReal.tsum_mul_left]
  unfold En
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun m => ?_
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg (wt_nonneg 0 m) (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  have := succ_pow_le (total m) p
  simp only [wt, pow_zero, one_mul]
  have hy := sq_nonneg ‖y m‖
  nlinarith

lemma ann_En_sum_le (p : ℕ) (x : Fock) :
    ∑' a : ℤ, En p (fun m => xcoord x m a) ≤ En (p+1) x := by
  rw [ann_energy_sum]
  refine ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  simp only [wt]
  exact pow_le_pow_left₀ (by positivity) (by linarith) _

lemma coeff_sum (h : H) (t : ℝ) :
    ∑' a : ℤ, ENNReal.ofReal (‖Complex.I * (t : ℂ) * inner ℂ (lp.single 2 a (1 : ℂ)) h‖^2) =
      ENNReal.ofReal (t^2 * ‖h‖^2) := by
  have h1 := lp.hasSum_norm (p := 2) (by norm_num) h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
  have h3 : HasSum (fun a : ℤ => t^2 * ‖h a‖^2) (t^2 * ‖h‖^2) := h1.mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) ?_]
  · congr 1
    rw [← h3.tsum_eq]
    refine tsum_congr fun a => ?_
    rw [lp.inner_single_left]
    simp [mul_pow, sq_abs]
  · exact (h3.summable.congr fun a => by
      rw [lp.inner_single_left]
      simp [mul_pow, sq_abs])

/-- The finite-particle energy estimate. -/
theorem core_energy (h : H) (t : ℝ) :
    ∀ p : ℕ, ∀ x : D, (∃ N, ParticleBound N x.1) →
      En p (unitary h t x.1) ≤ Cn (ENNReal.ofReal (t^2 * ‖h‖^2)) p * En p x.1 := by
  intro p
  induction p with
  | zero =>
    intro x _
    simp only [Cn, one_mul, En_zero, LinearIsometryEquiv.norm_map, le_refl]
  | succ p ih =>
    intro x ⟨N, hx⟩
    set B : ℝ≥0∞ := ENNReal.ofReal (t^2 * ‖h‖^2) with hB
    set y : Fock := unitary h t x.1 with hy
    let ea : ℤ → H := fun a => lp.single 2 a (1 : ℂ)
    let ca : ℤ → ℂ := fun a => Complex.I * (t : ℂ) * inner ℂ (ea a) h
    have hcoord (a : ℤ) : (fun m => xcoord y m a) =
        (fun m => (unitary h t (A (ea a) x).1) m) + ca a • (fun m => y m) := by
      funext m
      rw [← annC_single]
      have := core_ann (ea a) h t x hx m
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact this
    have hA : ∀ a, ∃ N', ParticleBound N' (A (ea a) x).1 := fun a =>
      ⟨N, A_particleBound (ea a) x hx⟩
    have hper (a : ℤ) : En p (fun m => xcoord y m a) ≤
        2 * (Cn B p * En p (fun m => xcoord x.1 m a)) +
          2 * (ENNReal.ofReal (‖ca a‖^2) * (Cn B p * En p x.1)) := by
      rw [hcoord a]
      refine (En_add_le p _ _).trans ?_
      rw [En_smul]
      have h1 := ih (A (ea a) x) (hA a)
      have h2 := ih x ⟨N, hx⟩
      have h3 : En p (A (ea a) x).1 = En p (fun m => xcoord x.1 m a) := by
        unfold En
        refine tsum_congr fun m => ?_
        rw [A_coord, annC_single]
      rw [h3] at h1
      gcongr
    have hsum : ∑' a : ℤ, En p (fun m => xcoord y m a) ≤
        2 * (Cn B p * (1 + B) * En (p+1) x.1) := by
      calc
        ∑' a : ℤ, En p (fun m => xcoord y m a)
            ≤ ∑' a : ℤ, (2 * (Cn B p * En p (fun m => xcoord x.1 m a)) +
              2 * (ENNReal.ofReal (‖ca a‖^2) * (Cn B p * En p x.1))) :=
          ENNReal.tsum_le_tsum hper
        _ = 2 * (Cn B p * ∑' a : ℤ, En p (fun m => xcoord x.1 m a)) +
              2 * (B * (Cn B p * En p x.1)) := by
            have e1 : ∑' a : ℤ, 2 * (Cn B p * En p (fun m => xcoord x.1 m a)) =
                2 * (Cn B p * ∑' a : ℤ, En p (fun m => xcoord x.1 m a)) := by
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
            have e2 : ∑' a : ℤ, 2 * (ENNReal.ofReal (‖ca a‖^2) * (Cn B p * En p x.1)) =
                2 * ((∑' a : ℤ, ENNReal.ofReal (‖ca a‖^2)) * (Cn B p * En p x.1)) := by
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
            have e3 : ∑' a : ℤ, ENNReal.ofReal (‖ca a‖^2) = B := coeff_sum h t
            rw [ENNReal.tsum_add, e1, e2, e3]
        _ ≤ 2 * (Cn B p * En (p+1) x.1) + 2 * (B * (Cn B p * En (p+1) x.1)) := by
            gcongr
            · exact ann_En_sum_le p x.1
            · exact En_mono (Nat.le_succ p) _
        _ = 2 * (Cn B p * (1 + B) * En (p+1) x.1) := by ring
    have hn : ENNReal.ofReal (‖y‖^2) ≤ En (p+1) x.1 := by
      rw [hy, LinearIsometryEquiv.norm_map]
      exact norm_sq_le_En _ _
    calc
      En (p+1) y ≤ 2^(p+1) * (∑' a : ℤ, En p (fun m => xcoord y m a)) +
          ENNReal.ofReal (‖y‖^2) := En_succ_le p y
      _ ≤ 2^(p+1) * (2 * (Cn B p * (1 + B) * En (p+1) x.1)) + En (p+1) x.1 := by
          gcongr
      _ = Cn B (p+1) * En (p+1) x.1 := by
          have hC : Cn B (p+1) = 2^(p+2) * Cn B p * (1 + B) + 1 := rfl
          rw [hC]
          ring

/-- The energy estimate for ALL vectors of the occupation Fock space. -/
theorem energy_bound (h : H) (t : ℝ) (p : ℕ) (x : Fock) :
    En p (unitary h t x) ≤ Cn (ENNReal.ofReal (t^2 * ‖h‖^2)) p * En p x := by
  let U := unitary h t
  let xD : ℕ → D := fun K => ⟨truncFock K x, truncFock_smooth K x⟩
  have hlim : Tendsto (fun K : ℕ => U (truncFock K x)) atTop (𝓝 (U x)) :=
    (U.continuous.tendsto x).comp (tendsto_truncFock x)
  have hK (K : ℕ) : En p (U (truncFock K x)) ≤ Cn (ENNReal.ofReal (t^2 * ‖h‖^2)) p * En p x := by
    refine (core_energy h t p (xD K) ⟨K, truncFock_particleBound K x⟩).trans ?_
    gcongr
    exact En_le_of_norm_le p (fun m => by
      change ‖truncFock K x m‖ ≤ ‖x m‖
      rw [truncFock_apply]
      by_cases hm : total m ≤ K <;> simp [hm])
  unfold En at hK ⊢
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  have hF : Tendsto (fun K : ℕ => ∑ m ∈ F, ENNReal.ofReal (wt p m * ‖U (truncFock K x) m‖^2))
      atTop (𝓝 (∑ m ∈ F, ENNReal.ofReal (wt p m * ‖U x m‖^2))) := by
    refine tendsto_finsetSum _ fun m _ => ?_
    have hc : Tendsto (fun K : ℕ => U (truncFock K x) m) atTop (𝓝 (U x m)) :=
      ((lp.evalCLM ℂ (fun _ : Occ => ℂ) 2 m).continuous.tendsto _).comp hlim
    have hr : Tendsto (fun K : ℕ => wt p m * ‖U (truncFock K x) m‖^2) atTop
        (𝓝 (wt p m * ‖U x m‖^2)) :=
      (hc.norm.pow 2).const_mul _
    exact (ENNReal.tendsto_ofReal hr)
  refine le_of_tendsto' hF fun K => ?_
  exact (ENNReal.sum_le_tsum F).trans (hK K)

/-- The displacement preserves every polynomial number-moment domain. -/
theorem En_unitary_ne_top (h : H) (t : ℝ) (p : ℕ) (x : Fock) (hx : En p x ≠ ⊤) :
    En p (unitary h t x) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (energy_bound h t p x)
  exact ENNReal.mul_ne_top (Cn_ne_top ENNReal.ofReal_ne_top p) hx

/-- The displacement preserves the common smooth domain. -/
theorem smooth_unitary (h : H) (t : ℝ) (x : Fock) (hx : Smooth x) :
    Smooth (unitary h t x) := by
  rw [smooth_iff_En] at hx ⊢
  exact fun p => En_unitary_ne_top h t p x (hx p)

end QuantumNLS.Prop024WEnergy

#print axioms QuantumNLS.Prop024WEnergy.core_energy
#print axioms QuantumNLS.Prop024WEnergy.energy_bound
#print axioms QuantumNLS.Prop024WEnergy.En_unitary_ne_top
#print axioms QuantumNLS.Prop024WEnergy.smooth_unitary

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WEnergy." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WEnergy." then
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
  Lean.logInfo m!"Prop024WEnergy aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
