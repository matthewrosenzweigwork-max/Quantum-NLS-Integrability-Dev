import QuantumNLS.FiniteCellTotalVariation

/-! R-D8BB052C H0/H: actual full-array events and action concentration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical
namespace QuantumNLS.FiniteCellEvents
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport
  FiniteCellPartition FiniteCellGauge FiniteCellTransport FiniteCellCoefficientLaw
  FiniteCellTotalVariation
variable {N : ℕ}

/-- The mass of an event in complete arrays. Exterior occupations are unrestricted. -/
def mass (g : H N) (E : Set (Arr N)) : ℝ := ∑' m : E, law g m.1

theorem mass_nonneg (g : H N) (E : Set (Arr N)) : 0 ≤ mass g E :=
  tsum_nonneg (fun m => law_nonneg g m.1)

/-- Disintegration over any event, for the actual pushforward law. -/
theorem pushLaw_event {X : Type*} (f : Arr N → X) (g : H N) (E : Set X) :
    (∑' x : E, pushLaw f g x.1) = mass g (f ⁻¹' E) := by
  let F : (f ⁻¹' E) → E := fun m => ⟨f m.1, m.2⟩
  have hs := ((law_summable g).subtype (fun m => f m ∈ E)).hasSum.tsum_fiberwise F
  have he : ∀ x : E, (∑' m : F ⁻¹' {x}, law g m.1.1) = pushLaw f g x.1 := by
    intro x
    let e : (F ⁻¹' {x}) ≃ (f ⁻¹' {x.1}) :=
      { toFun := fun m => ⟨m.1.1, congrArg Subtype.val m.2⟩
        invFun := fun m => ⟨⟨m.1, by change f m.1 ∈ E; rw [show f m.1 = x.1 from m.2]; exact x.2⟩,
          Subtype.ext m.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.tsum_eq (fun m => law g m.1)
  change HasSum (fun x : E => ∑' m : F ⁻¹' {x}, law g m.1.1) (mass g (f ⁻¹' E)) at hs
  simp_rw [he] at hs
  exact hs.tsum_eq

/-- An event translated by an equivalence is still summed over every full fiber. -/
theorem pushLaw_translated_event {X : Type*} (f : Arr N → X) (g : H N)
    (e : X ≃ X) (E : Set X) :
    (∑' x : E, pushLaw f g (e x.1)) = mass g (f ⁻¹' (e.symm ⁻¹' E)) := by
  let d : E ≃ (e.symm ⁻¹' E) :=
    { toFun := fun x => ⟨e x.1, by simp only [Set.mem_preimage, e.symm_apply_apply]; exact x.2⟩
      invFun := fun x => ⟨e.symm x.1, x.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1) }
  rw [← pushLaw_event f g (e.symm ⁻¹' E)]
  exact d.tsum_eq (fun x => pushLaw f g x.1)

theorem selected_event (I : Finset ℤ) (g : H N) (E : Set (↥I → ℤ)) :
    (∑' k : E, pushLaw (selected (N := N) I) g k.1) =
      mass g ((selected (N := N) I) ⁻¹' E) := pushLaw_event _ _ _

theorem selected_translated_event (I : Finset ℤ) (a b : ℤ) (g : H N)
    (E : Set (↥I → ℤ)) :
    (∑' k : E, pushLaw (selected (N := N) I) g (selectedStep I a b k.1)) =
      mass g ((selected (N := N) I) ⁻¹' ((selectedStep I b a) ⁻¹' E)) :=
  pushLaw_translated_event _ _ (selectedStepEquiv I a b) E

/-- G's actual residual estimate, now on full-array event masses. -/
theorem full_event_from_residual_sum (I G : Finset ℤ) (c : OrderedSeeds N) (t : ℤ → Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : FiniteCellEstimate.Pairs G, ‖FiniteCellEstimate.pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (ha : a ∈ G) (hb : b ∈ G) (hab : a ≠ b) (E : Set (↥I → ℤ)) :
    |mass g ((selected (N := N) I) ⁻¹' E) -
      mass g ((selected (N := N) I) ⁻¹' ((selectedStep I b a) ⁻¹' E))| ≤ Real.sqrt (2 * eta) := by
  rw [← selected_event, ← selected_translated_event I a b]
  exact selected_event_from_residual_sum I G c t g hg eta heta hres a b ha hb hab E

/-- Exact coefficient of the actual diagonal action residual. -/
theorem action_residual_apply (c : ℤ) (a : ℝ) (g : H N) (m : Arr N) :
    (E N c c g - (a : ℂ) • g) m =
      (((m.1 c : ℝ) / (N : ℝ) - a : ℝ) : ℂ) * g m := by
  change E N c c g m - (a : ℂ) * g m = _
  rw [E_diag_apply, coef_diag, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

theorem action_residual_energy_term (c : ℤ) (a : ℝ) (g : H N) (m : Arr N) :
    ‖(E N c c g - (a : ℂ) • g) m‖ ^ 2 =
      ((m.1 c : ℝ) / (N : ℝ) - a) ^ 2 * law g m := by
  rw [action_residual_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

/-- Actual diagonal action energy, including its summability. -/
theorem action_residual_energy (c : ℤ) (a : ℝ) (g : H N) :
    Summable (fun m : Arr N => ((m.1 c : ℝ) / (N : ℝ) - a) ^ 2 * law g m) ∧
    ‖E N c c g - (a : ℂ) • g‖ ^ 2 =
      ∑' m : Arr N, ((m.1 c : ℝ) / (N : ℝ) - a) ^ 2 * law g m := by
  refine ⟨(summable_energy _).congr (action_residual_energy_term c a g), ?_⟩
  rw [← tsum_energy]
  exact tsum_congr (action_residual_energy_term c a g)

/-- The printed ceiling threshold satisfies both required quotient bounds. -/
theorem threshold_ratio (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N) :
    (1 : ℝ) / ell ≤ (threshold N ell : ℝ) / N ∧
      (threshold N ell : ℝ) / N ≤ 2 / ell := by
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hen : (ell : ℝ) ≤ N := by exact_mod_cast hN
  have hlo := Nat.le_ceil ((N : ℝ) / ell)
  have hhi := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (N : ℝ) / ell)
  change (N : ℝ) / ell ≤ (threshold N ell : ℝ) at hlo
  change (threshold N ell : ℝ) < (N : ℝ) / ell + 1 at hhi
  constructor
  · apply (le_div_iff₀ hn).mpr
    calc
      (1 : ℝ) / ell * N = (N : ℝ) / ell := by ring
      _ ≤ (threshold N ell : ℝ) := hlo
  · apply (div_le_iff₀ hn).mpr
    have hfrac : (1 : ℝ) ≤ (N : ℝ) / ell := (le_div_iff₀ he).mpr (by simpa using hen)
    calc
      (threshold N ell : ℝ) ≤ (N : ℝ) / ell + 1 := hhi.le
      _ ≤ 2 * ((N : ℝ) / ell) := by linarith
      _ = 2 / (ell : ℝ) * N := by ring

/-- Event mass is monotone under inclusion. -/
theorem mass_mono (g : H N) {A B : Set (Arr N)} (h : A ⊆ B) : mass g A ≤ mass g B := by
  let j : A → B := fun m => ⟨m.1, h m.2⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : B => z.1) he
  have hb := (law_summable g).subtype (· ∈ B)
  exact (hb.comp_injective hj).tsum_le_tsum_of_inj j hj
    (fun m _ => law_nonneg g m.1) (fun _ => le_rfl) hb

/-- Countable Chebyshev on the actual action coefficients. -/
theorem action_concentration (c : ℤ) (a delta C : ℝ) (hdelta : 0 ≤ delta)
    (hC : 0 ≤ C) (g : H N) (herr : ‖E N c c g - (a : ℂ) • g‖ ≤ delta)
    (A : Set (Arr N))
    (hgap : ∀ m ∈ A, 1 ≤ C * ((m.1 c : ℝ) / N - a) ^ 2) :
    mass g A ≤ C * delta ^ 2 := by
  let en : Arr N → ℝ := fun m => ((m.1 c : ℝ) / N - a) ^ 2 * law g m
  have he := action_residual_energy c a g
  have hs := (law_summable g).subtype (· ∈ A)
  have ht := (he.1.mul_left C).subtype (· ∈ A)
  have hpoint : ∀ m : A, law g m.1 ≤ C * en m.1 := by
    intro m
    have h := mul_le_mul_of_nonneg_right (hgap m.1 m.2) (law_nonneg g m.1)
    simpa only [one_mul, mul_assoc, en] using h
  have hi := Summable.tsum_subtype_le (fun m => C * en m) A
    (fun m => mul_nonneg hC (mul_nonneg (sq_nonneg _) (law_nonneg g m))) (he.1.mul_left C)
  have hbound : ‖E N c c g - (a : ℂ) • g‖ ^ 2 ≤ delta ^ 2 :=
    by nlinarith [norm_nonneg (E N c c g - (a : ℂ) • g)]
  calc
    mass g A ≤ ∑' m : A, C * en m.1 := hs.tsum_le_tsum hpoint ht
    _ ≤ ∑' m, C * en m := hi
    _ = C * ‖E N c c g - (a : ℂ) • g‖ ^ 2 := by rw [tsum_mul_left, ← he.2]
    _ ≤ C * delta ^ 2 := mul_le_mul_of_nonneg_left hbound hC

/-- A finite union bound for complete-array events. -/
theorem mass_finite_union {X : Type*} (S : Finset X) (A : X → Set (Arr N)) (g : H N) :
    mass g {m | ∃ c ∈ S, m ∈ A c} ≤ ∑ c ∈ S, mass g (A c) := by
  have hs : ∀ c, Summable ((A c).indicator (law g)) := fun c => (law_summable g).indicator _
  unfold mass
  simp_rw [tsum_subtype]
  rw [← Summable.tsum_finsetSum (fun c _ => hs c)]
  apply Summable.tsum_le_tsum _ ((law_summable g).indicator _) (summable_sum (fun c _ => hs c))
  intro m
  by_cases hm : ∃ c ∈ S, m ∈ A c
  · obtain ⟨c,hc,hmc⟩ := hm
    rw [Set.indicator_of_mem (show m ∈ {m | ∃ c ∈ S, m ∈ A c} from ⟨c,hc,hmc⟩)]
    exact (show law g m = (A c).indicator (law g) m by rw [Set.indicator_of_mem hmc]).le.trans
      (Finset.single_le_sum (fun d _ => Set.indicator_nonneg (fun m _ => law_nonneg g m) _)
        hc)
  · rw [Set.indicator_of_notMem (show m ∉ {m | ∃ c ∈ S, m ∈ A c} from hm)]
    exact Finset.sum_nonneg (fun c _ => Set.indicator_nonneg (fun m _ => law_nonneg g m) _)

/-- A selected coordinate well above the threshold cannot have a small count
except on the event forced by its actual action error. -/
theorem endpoint_low_count (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : ℤ) (a delta : ℝ) (hdelta : 0 ≤ delta) (ha : 4 / (ell : ℝ) ≤ a)
    (g : H N) (herr : ‖E N c c g - (a : ℂ) • g‖ ≤ delta) :
    mass g {m : Arr N | m.1 c ≤ threshold N ell} ≤ (ell : ℝ) ^ 2 * delta ^ 2 := by
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply action_concentration c a delta ((ell : ℝ) ^ 2) hdelta (sq_nonneg _) g herr
  intro m hm
  have hm' : (m.1 c : ℝ) / N ≤ (threshold N ell : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) hn.le
  have htop := (threshold_ratio ell hell hN).2
  have hgap : 1 / (ell : ℝ) ≤ a - (m.1 c : ℝ) / N := by
    have hp : (0 : ℝ) ≤ 1 / (ell : ℝ) := by positivity
    simp only [div_eq_mul_inv, one_mul] at ha hm' htop hp ⊢
    linarith
  have hmul : (1 : ℝ) ≤ (a - (m.1 c : ℝ) / N) * ell := (div_le_iff₀ he).mp hgap
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmul 2
  nlinarith

/-- The strict endpoint and receiver boundary bounds follow from the same action error. -/
theorem endpoint_strict_count (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : ℤ) (a delta : ℝ) (hdelta : 0 ≤ delta) (ha : 4 / (ell : ℝ) ≤ a)
    (g : H N) (herr : ‖E N c c g - (a : ℂ) • g‖ ≤ delta) :
    mass g {m : Arr N | m.1 c < threshold N ell} ≤ (ell : ℝ) ^ 2 * delta ^ 2 :=
  (mass_mono g (fun _ h => Nat.le_of_lt h)).trans (endpoint_low_count ell hell hN c a delta hdelta ha g herr)

theorem endpoint_zero_count (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : ℤ) (a delta : ℝ) (hdelta : 0 ≤ delta) (ha : 4 / (ell : ℝ) ≤ a)
    (g : H N) (herr : ‖E N c c g - (a : ℂ) • g‖ ≤ delta) :
    mass g {m : Arr N | m.1 c = 0} ≤ (ell : ℝ) ^ 2 * delta ^ 2 :=
  (mass_mono g (fun _ h => by dsimp at h ⊢; rw [h]; exact Nat.zero_le _)).trans
    (endpoint_low_count ell hell hN c a delta hdelta ha g herr)

/-- Chebyshev for an active coordinate whose target is below the good-set cutoff. -/
theorem active_small_target (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (c : ℤ) (a delta : ℝ) (hdelta : 0 ≤ delta)
    (g : H N) (herr : ‖E N c c g - (a : ℂ) • g‖ ≤ delta) :
    mass g {m : Arr N | threshold N ell ≤ m.1 c ∧ a < 1 / (2 * (ell : ℝ))} ≤
      4 * (ell : ℝ) ^ 2 * delta ^ 2 := by
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply action_concentration c a delta (4 * (ell : ℝ) ^ 2) hdelta (by positivity) g herr
  intro m hm
  have hm' : (threshold N ell : ℝ) / N ≤ (m.1 c : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm.1) hn.le
  have hbot := (threshold_ratio ell hell hN).1
  have hhalf : (1 : ℝ) / ell = 2 * (1 / (2 * (ell : ℝ))) := by field_simp
  have hgap : 1 / (2 * (ell : ℝ)) ≤ (m.1 c : ℝ) / N - a := by linarith [hm.2]
  have hmul : (1 : ℝ) ≤ ((m.1 c : ℝ) / N - a) * (2 * ell) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ell)).mp hgap
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmul 2
  nlinarith

/-- The exact printed active-set probability bound, derived only from actual action errors. -/
theorem active_not_good (I : Finset ℤ) (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (a : ℤ → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta) (g : H N)
    (herr : ∀ c ∈ I, ‖E N c c g - (a c : ℂ) • g‖ ≤ delta) :
    mass g {m : Arr N | ¬ active I (threshold N ell) m ⊆ I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ a c)} ≤
      4 * (I.card : ℝ) * (ell : ℝ) ^ 2 * delta ^ 2 := by
  let A : ℤ → Set (Arr N) := fun c => {m | threshold N ell ≤ m.1 c ∧ a c < 1 / (2 * (ell : ℝ))}
  have hin : {m : Arr N | ¬ active I (threshold N ell) m ⊆ I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ a c)} ⊆
      {m : Arr N | ∃ c ∈ I, m ∈ A c} := by
    intro m hm
    change ¬ ∀ c ∈ active I (threshold N ell) m, c ∈ I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ a c) at hm
    push Not at hm
    obtain ⟨c,hc,hbad⟩ := hm
    have hc' := Finset.mem_filter.mp hc
    refine ⟨c,hc'.1,hc'.2,?_⟩
    have hb : ¬ 1 / (2 * (ell : ℝ)) ≤ a c := fun h => hbad (Finset.mem_filter.mpr ⟨hc'.1,h⟩)
    exact lt_of_not_ge hb
  calc
    _ ≤ mass g {m : Arr N | ∃ c ∈ I, m ∈ A c} := mass_mono g hin
    _ ≤ ∑ c ∈ I, mass g (A c) := mass_finite_union I A g
    _ ≤ ∑ _c ∈ I, 4 * (ell : ℝ) ^ 2 * delta ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      exact active_small_target ell hell hN c (a c) delta hdelta g (herr c hc)
    _ = 4 * (I.card : ℝ) * (ell : ℝ) ^ 2 * delta ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end QuantumNLS.FiniteCellEvents

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellEvents.mass
#print axioms QuantumNLS.FiniteCellEvents.mass_nonneg
#print axioms QuantumNLS.FiniteCellEvents.pushLaw_event
#print axioms QuantumNLS.FiniteCellEvents.pushLaw_translated_event
#print axioms QuantumNLS.FiniteCellEvents.selected_event
#print axioms QuantumNLS.FiniteCellEvents.selected_translated_event
#print axioms QuantumNLS.FiniteCellEvents.full_event_from_residual_sum
#print axioms QuantumNLS.FiniteCellEvents.action_residual_apply
#print axioms QuantumNLS.FiniteCellEvents.action_residual_energy_term
#print axioms QuantumNLS.FiniteCellEvents.action_residual_energy
#print axioms QuantumNLS.FiniteCellEvents.threshold_ratio
#print axioms QuantumNLS.FiniteCellEvents.mass_mono
#print axioms QuantumNLS.FiniteCellEvents.action_concentration
#print axioms QuantumNLS.FiniteCellEvents.mass_finite_union
#print axioms QuantumNLS.FiniteCellEvents.endpoint_low_count
#print axioms QuantumNLS.FiniteCellEvents.endpoint_strict_count
#print axioms QuantumNLS.FiniteCellEvents.endpoint_zero_count
#print axioms QuantumNLS.FiniteCellEvents.active_small_target
#print axioms QuantumNLS.FiniteCellEvents.active_not_good

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellEvents.mass,
    ``QuantumNLS.FiniteCellEvents.mass_nonneg,
    ``QuantumNLS.FiniteCellEvents.pushLaw_event,
    ``QuantumNLS.FiniteCellEvents.pushLaw_translated_event,
    ``QuantumNLS.FiniteCellEvents.selected_event,
    ``QuantumNLS.FiniteCellEvents.selected_translated_event,
    ``QuantumNLS.FiniteCellEvents.full_event_from_residual_sum,
    ``QuantumNLS.FiniteCellEvents.action_residual_apply,
    ``QuantumNLS.FiniteCellEvents.action_residual_energy_term,
    ``QuantumNLS.FiniteCellEvents.action_residual_energy,
    ``QuantumNLS.FiniteCellEvents.threshold_ratio,
    ``QuantumNLS.FiniteCellEvents.mass_mono,
    ``QuantumNLS.FiniteCellEvents.action_concentration,
    ``QuantumNLS.FiniteCellEvents.mass_finite_union,
    ``QuantumNLS.FiniteCellEvents.endpoint_low_count,
    ``QuantumNLS.FiniteCellEvents.endpoint_strict_count,
    ``QuantumNLS.FiniteCellEvents.endpoint_zero_count,
    ``QuantumNLS.FiniteCellEvents.active_small_target,
    ``QuantumNLS.FiniteCellEvents.active_not_good]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellEvents aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
