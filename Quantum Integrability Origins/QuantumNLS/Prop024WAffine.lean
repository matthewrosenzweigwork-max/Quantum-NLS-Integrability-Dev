import QuantumNLS.Prop024WEnergy

/-! PROP-024 affine Weyl action, module 4: the affine identities on the whole smooth domain `D`
(occupation coordinates), as identities of endomorphisms of `D`.

For the frozen EXT-006 unitary `U_t = unitary h t = exp(i t (a*(h)+a(h)))`:

* `U_t` restricts to a linear automorphism `Ud h t` of the smooth domain `D` (module 3 supplies
  the domain statement; the group law is the frozen `unitary_add`/`unitary_zero`);
* `a(g) U_t = U_t (a(g) + i t ⟨g,h⟩)` and `a*(g) U_t = U_t (a*(g) - i t ⟨h,g⟩)` in `End D`,
  with `⟨·,·⟩` linear in the second slot (extended from the finite-particle core by the
  `1_{total ≤ K}` truncations);
* equivalently `U_t⁻¹ a(g) U_t = a(g) + i t ⟨g,h⟩`.

No Weyl/interaction compatibility premise; no sorry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal Topology
open Filter
namespace QuantumNLS.Prop024WAffine
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmoothOperatorsR34a Ext006FieldBoundsR42a Ext006StrongFieldR41a
open Ext006BoundedExponentialR43a Ext006SeriesIdentificationR43a
open Prop024WCoordinates Prop024WCoreAffine Prop024WEnergy

/-- Coordinate evaluation as a continuous linear functional. -/
def coordCLM (m : Occ) : Fock →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : Occ => ℂ) 2 m

lemma coordCLM_apply (m : Occ) (y : Fock) : coordCLM m y = y m := rfl

/-- The finite-particle truncation as an element of the smooth domain. -/
def truncD (K : ℕ) (x : D) : D := ⟨truncFock K x.1, truncFock_smooth K x.1⟩

lemma truncD_coe (K : ℕ) (x : D) : (truncD K x).1 = truncFock K x.1 := rfl

lemma sub_truncD_coord (K : ℕ) (x : D) (m : Occ) :
    (x - truncD K x).1 m = if K < total m then x.1 m else 0 := by
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, truncD_coe, truncFock_apply]
  by_cases hm : total m ≤ K
  · simp [hm, not_lt.mpr hm]
  · simp [hm, not_le.mp hm]

lemma tendsto_zero_of_sq_le {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (R : ℕ → ℝ)
    (hR : Tendsto R atTop (𝓝 0)) (hv : ∀ K, ‖v K‖^2 ≤ R K) : Tendsto v atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hR
  rw [Real.sqrt_zero] at h2
  refine squeeze_zero (fun K => norm_nonneg _) (fun K => ?_) h2
  have := Real.abs_le_sqrt (hv K)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The weighted tail of a smooth vector vanishes. -/
lemma tail_mass_tendsto (x : D) :
    Tendsto (fun K : ℕ => ∑' m : Occ, (if K < total m then (total m : ℝ) * ‖x.1 m‖^2 else 0))
      atTop (𝓝 0) := by
  refine tail_tendsto (fun m => (total m : ℝ) * ‖x.1 m‖^2) ?_ (fun m => by positivity)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (x.2 1)
  simp only [pow_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

lemma A_tail_sq_le (g : H) (K : ℕ) (x : D) :
    ‖(A g (x - truncD K x)).1‖^2 ≤
      ‖g‖^2 * ∑' m : Occ, (if K < total m then (total m : ℝ) * ‖x.1 m‖^2 else 0) := by
  refine (A_norm_sq_le_mass g (x - truncD K x)).trans ?_
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (sq_nonneg _)
  refine tsum_congr fun m => ?_
  rw [sub_truncD_coord]
  by_cases hm : K < total m <;> simp [hm]

lemma tendsto_A_trunc (g : H) (x : D) :
    Tendsto (fun K : ℕ => (A g (truncD K x)).1) atTop (𝓝 (A g x).1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_zero_of_sq_le _ (fun K => ‖g‖^2 *
    ∑' m : Occ, (if K < total m then (total m : ℝ) * ‖x.1 m‖^2 else 0)) ?_ (fun K => ?_)
  · simpa using (tail_mass_tendsto x).const_mul (‖g‖^2)
  · have := A_tail_sq_le g K x
    rwa [map_sub, Submodule.coe_sub, norm_sub_rev] at this

lemma tendsto_C_trunc (g : H) (x : D) :
    Tendsto (fun K : ℕ => (C g (truncD K x)).1) atTop (𝓝 (C g x).1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, ← tendsto_zero_iff_norm_tendsto_zero]
  have hn : Tendsto (fun K : ℕ => ‖x.1 - truncFock K x.1‖^2) atTop (𝓝 0) := by
    simp only [norm_sq_sub_truncFock]
    exact tail_tendsto (fun m => ‖x.1 m‖^2) (summable_sq x.1) (fun m => sq_nonneg _)
  refine tendsto_zero_of_sq_le _ (fun K => ‖g‖^2 *
      ∑' m : Occ, (if K < total m then (total m : ℝ) * ‖x.1 m‖^2 else 0) +
      ‖g‖^2 * ‖x.1 - truncFock K x.1‖^2) ?_ (fun K => ?_)
  · simpa using ((tail_mass_tendsto x).const_mul (‖g‖^2)).add (hn.const_mul (‖g‖^2))
  · have hC := C_norm_sq g (x - truncD K x)
    have e : ‖(C g (truncD K x)).1 - (C g x).1‖ = ‖(C g (x - truncD K x)).1‖ := by
      rw [map_sub, Submodule.coe_sub, norm_sub_rev]
    rw [e, hC]
    have := A_tail_sq_le g K x
    have h2 : ‖(x - truncD K x).1‖ = ‖x.1 - truncFock K x.1‖ := rfl
    rw [h2]
    linarith

/-- Annihilation affine identity on all smooth vectors. -/
theorem ann_affine (g h : H) (t : ℝ) (x : D) (m : Occ) :
    annC g m (unitary h t x.1) =
      (unitary h t (A g x).1) m + (Complex.I * (t : ℂ) * inner ℂ g h) * (unitary h t x.1) m := by
  set c : ℂ := Complex.I * (t : ℂ) * inner ℂ g h with hc
  have hU : Tendsto (fun K : ℕ => unitary h t (truncD K x).1) atTop (𝓝 (unitary h t x.1)) :=
    ((unitary h t).continuous.tendsto _).comp (tendsto_truncFock x.1)
  have hAU : Tendsto (fun K : ℕ => unitary h t (A g (truncD K x)).1) atTop
      (𝓝 (unitary h t (A g x).1)) :=
    ((unitary h t).continuous.tendsto _).comp (tendsto_A_trunc g x)
  have hL : Tendsto (fun K : ℕ => annC g m (unitary h t (truncD K x).1)) atTop
      (𝓝 (annC g m (unitary h t x.1))) :=
    ((annC g m).continuous.tendsto _).comp hU
  have hR : Tendsto (fun K : ℕ => (unitary h t (A g (truncD K x)).1) m +
      c * (unitary h t (truncD K x).1) m) atTop
      (𝓝 ((unitary h t (A g x).1) m + c * (unitary h t x.1) m)) := by
    have h1 := ((coordCLM m).continuous.tendsto _).comp hAU
    have h2 := ((coordCLM m).continuous.tendsto _).comp hU
    exact h1.add (h2.const_mul c)
  refine tendsto_nhds_unique
    (hL.congr (fun K => core_ann g h t (truncD K x) (truncFock_particleBound K x.1) m)) hR

/-- Creation affine identity on all smooth vectors. -/
theorem cre_affine (g h : H) (t : ℝ) (x : D) (m : Occ) :
    creC g m (unitary h t x.1) =
      (unitary h t (C g x).1) m +
        (Complex.I * (t : ℂ) * (-(inner ℂ h g))) * (unitary h t x.1) m := by
  set c : ℂ := Complex.I * (t : ℂ) * (-(inner ℂ h g)) with hc
  have hU : Tendsto (fun K : ℕ => unitary h t (truncD K x).1) atTop (𝓝 (unitary h t x.1)) :=
    ((unitary h t).continuous.tendsto _).comp (tendsto_truncFock x.1)
  have hAU : Tendsto (fun K : ℕ => unitary h t (C g (truncD K x)).1) atTop
      (𝓝 (unitary h t (C g x).1)) :=
    ((unitary h t).continuous.tendsto _).comp (tendsto_C_trunc g x)
  have hL : Tendsto (fun K : ℕ => creC g m (unitary h t (truncD K x).1)) atTop
      (𝓝 (creC g m (unitary h t x.1))) :=
    ((creC g m).continuous.tendsto _).comp hU
  have hR : Tendsto (fun K : ℕ => (unitary h t (C g (truncD K x)).1) m +
      c * (unitary h t (truncD K x).1) m) atTop
      (𝓝 ((unitary h t (C g x).1) m + c * (unitary h t x.1) m)) := by
    have h1 := ((coordCLM m).continuous.tendsto _).comp hAU
    have h2 := ((coordCLM m).continuous.tendsto _).comp hU
    exact h1.add (h2.const_mul c)
  refine tendsto_nhds_unique
    (hL.congr (fun K => core_cre g h t (truncD K x) (truncFock_particleBound K x.1) m)) hR

/-! ### The displacement as an automorphism of the smooth domain -/

/-- `U_t` restricted to the smooth domain: it maps `D` into `D` (module 3). -/
def Ud (h : H) (t : ℝ) : Module.End ℂ D where
  toFun x := ⟨unitary h t x.1, smooth_unitary h t x.1 x.2⟩
  map_add' x y := Subtype.ext (map_add (unitary h t) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (unitary h t) c x.1)

lemma Ud_coe (h : H) (t : ℝ) (x : D) : (Ud h t x).1 = unitary h t x.1 := rfl

lemma Ud_zero (h : H) : Ud h 0 = 1 :=
  LinearMap.ext fun x => Subtype.ext (unitary_zero h x.1)

lemma Ud_mul (h : H) (s t : ℝ) : Ud h s * Ud h t = Ud h (s+t) :=
  LinearMap.ext fun x => Subtype.ext (unitary_add h s t x.1)

lemma Ud_neg_mul (h : H) (t : ℝ) : Ud h (-t) * Ud h t = 1 := by
  rw [Ud_mul, neg_add_cancel, Ud_zero]

lemma Ud_mul_neg (h : H) (t : ℝ) : Ud h t * Ud h (-t) = 1 := by
  rw [Ud_mul, add_neg_cancel, Ud_zero]

/-- The annihilation Weyl relation `a(g) U_t = U_t (a(g) + i t ⟨g,h⟩)` in `End D`. -/
theorem A_Ud (g h : H) (t : ℝ) :
    A g * Ud h t = Ud h t * (A g + (Complex.I * (t : ℂ) * inner ℂ g h) • (1 : Module.End ℂ D)) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun m => ?_))
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [A_coord, Ud_coe]
  have := ann_affine g h t x m
  rw [this, Ud_coe, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, lp.coeFn_smul]

/-- The creation Weyl relation `a*(g) U_t = U_t (a*(g) - i t ⟨h,g⟩)` in `End D`. -/
theorem C_Ud (g h : H) (t : ℝ) :
    C g * Ud h t =
      Ud h t * (C g + (Complex.I * (t : ℂ) * (-(inner ℂ h g))) • (1 : Module.End ℂ D)) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun m => ?_))
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [C_coord, Ud_coe]
  have := cre_affine g h t x m
  rw [this, Ud_coe, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, lp.coeFn_smul]

/-- Conjugated form: `U_t⁻¹ a(g) U_t = a(g) + i t ⟨g,h⟩`. -/
theorem Ud_conj_A (g h : H) (t : ℝ) :
    Ud h (-t) * A g * Ud h t =
      A g + (Complex.I * (t : ℂ) * inner ℂ g h) • (1 : Module.End ℂ D) := by
  rw [mul_assoc, A_Ud, ← mul_assoc, Ud_neg_mul, one_mul]

/-- Conjugated form: `U_t⁻¹ a*(g) U_t = a*(g) - i t ⟨h,g⟩`. -/
theorem Ud_conj_C (g h : H) (t : ℝ) :
    Ud h (-t) * C g * Ud h t =
      C g + (Complex.I * (t : ℂ) * (-(inner ℂ h g))) • (1 : Module.End ℂ D) := by
  rw [mul_assoc, C_Ud, ← mul_assoc, Ud_neg_mul, one_mul]

end QuantumNLS.Prop024WAffine

#print axioms QuantumNLS.Prop024WAffine.ann_affine
#print axioms QuantumNLS.Prop024WAffine.cre_affine
#print axioms QuantumNLS.Prop024WAffine.A_Ud
#print axioms QuantumNLS.Prop024WAffine.C_Ud
#print axioms QuantumNLS.Prop024WAffine.Ud_conj_A
#print axioms QuantumNLS.Prop024WAffine.Ud_conj_C

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WAffine." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WAffine." then
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
  Lean.logInfo m!"Prop024WAffine aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
