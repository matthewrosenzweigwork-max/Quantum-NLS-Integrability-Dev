import QuantumNLS.Ext025SCalculus

/-! GP-13 application binding for R-2E4C2F4E, A06:domains. The fixed
majorant is the actual joint graph weight times the actual Bethe coefficient
square. Finite-label truncations approximate simultaneously in every selected
charge graph norm. No convergence or summability conclusion is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025B6GraphCore
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exactly the source graph density, including the ambient L² term. -/
def density {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (v : HN L N)
    (m : MArr N) : ℝ :=
  ‖b.repr v m‖^2 + ∑ j, |a j m|^2 * ‖b.repr v m‖^2

theorem density_eq {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (m : MArr N) :
    density b a v m = (1 + ∑ j, |a j m|^2) * ‖b.repr v m‖^2 := by
  simp only [density,add_mul,one_mul,Finset.sum_mul]

theorem density_nonneg {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (m : MArr N) : 0 ≤ density b a v m := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The actual weighted majorant is summable exactly on the common domain. -/
theorem summable_density_iff {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) : Summable (density b a v) ↔ ∀ j, v ∈ (multiplier b (a j)).domain := by
  have hterm (j : Fin d) (m : MArr N) : 0 ≤ |a j m|^2 * ‖b.repr v m‖^2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · intro h j
    apply (mem_domain b (a j) v).mpr
    simp only [← HilbertBasis.repr_apply_apply]
    apply Summable.of_nonneg_of_le (hterm j) _ h
    intro m
    exact (Finset.single_le_sum (fun k _ => hterm k m) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left (sq_nonneg _))
  · intro h
    have hs : ∀ F : Finset (Fin d), Summable (fun m => ∑ j ∈ F, |a j m|^2 * ‖b.repr v m‖^2) := by
      intro F
      induction F using Finset.induction_on with
      | empty => simp only [Finset.sum_empty] ; exact (summable_zero : Summable (fun _ : MArr N => (0 : ℝ)))
      | @insert j F hj ih =>
        simp only [Finset.sum_insert hj]
        have hjS : Summable (fun m => |a j m|^2 * ‖b.repr v m‖^2) := by
          simpa only [HilbertBasis.repr_apply_apply] using (mem_domain b (a j) v).mp (h j)
        exact hjS.add ih
    exact (Energy.summable_sq (b.repr v)).add (hs Finset.univ)

/-- Every support mask preserves the entire maximal graph domain. -/
theorem projection_mem (b : BetheBasis L N) (a : MArr N → ℝ)
    (s : Set (MArr N)) (v : HN L N) (hv : v ∈ (multiplier b a).domain) :
    projection b s v ∈ (multiplier b a).domain := by
  change Memℓp (fun m => (a m : ℂ) * b.repr (projection b s v) m) 2
  apply hv.mono'
  intro m
  rw [projection_coord]
  split_ifs <;> simp [mul_nonneg (abs_nonneg _) (norm_nonneg _)]

theorem projection_commutes (b : BetheBasis L N) (a : MArr N → ℝ)
    (s : Set (MArr N)) (v : HN L N) (hv : v ∈ (multiplier b a).domain) :
    multiplier b a ⟨projection b s v,projection_mem b a s v hv⟩ =
      projection b s (multiplier b a ⟨v,hv⟩) := by
  have hc (w : (multiplier b a).domain) (m : MArr N) :
      b.repr (multiplier b a w) m = (a m : ℂ) * b.repr w.val m := by
    simpa only [HilbertBasis.repr_apply_apply] using multiplier_coord b a w m
  apply b.repr.injective
  ext m
  rw [hc,projection_coord,projection_coord,hc]
  split_ifs <;> simp

/-- The actual squared joint graph error; no graph topology is left implicit. -/
def error {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (hv : ∀ j, v ∈ (multiplier b (a j)).domain) (s : Set (MArr N)) : ℝ :=
  ‖v-projection b s v‖^2 + ∑ j,
    ‖multiplier b (a j) ⟨v,hv j⟩ -
      multiplier b (a j) ⟨projection b s v,projection_mem b (a j) s v (hv j)⟩‖^2

/-- Parseval identifies each truncation error with its actual coefficient tail. -/
theorem vector_error (b : BetheBasis L N) (s : Set (MArr N)) (v : HN L N) :
    ‖v-projection b s v‖^2 = ∑' m, if m ∈ s then 0 else ‖b.repr v m‖^2 := by
  rw [← b.repr.norm_map,Energy.norm_sq_eq_tsum]
  apply tsum_congr
  intro m
  simp only [map_sub,lp.coeFn_sub,Pi.sub_apply,projection_coord]
  split_ifs <;> simp

theorem graph_error_eq {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (hv : ∀ j, v ∈ (multiplier b (a j)).domain) (s : Set (MArr N)) :
    error b a v hv s = ∑' m, if m ∈ s then 0 else density b a v m := by
  have ht (j : Fin d) : Summable (fun m => if m ∈ s then 0 else |a j m|^2 * ‖b.repr v m‖^2) := by
    apply Summable.of_nonneg_of_le
      (fun m => by split_ifs <;> positivity) (fun m => ?_)
      (by simpa only [← HilbertBasis.repr_apply_apply] using (mem_domain b (a j) v).mp (hv j))
    split_ifs <;> first | exact le_rfl | positivity
  have ht0 : Summable (fun m => if m ∈ s then 0 else ‖b.repr v m‖^2) := by
    apply Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => ?_) (Energy.summable_sq (b.repr v))
    split_ifs <;> first | exact le_rfl | positivity
  unfold error
  rw [vector_error]
  have he (j : Fin d) :
      ‖multiplier b (a j) ⟨v,hv j⟩ -
        multiplier b (a j) ⟨projection b s v,projection_mem b (a j) s v (hv j)⟩‖^2 =
      ∑' m, if m ∈ s then 0 else |a j m|^2 * ‖b.repr v m‖^2 := by
    rw [projection_commutes b (a j) s v (hv j),vector_error]
    apply tsum_congr
    intro m
    have hc : b.repr (multiplier b (a j) ⟨v,hv j⟩) m = (a j m : ℂ) * b.repr v m := by
      simpa only [HilbertBasis.repr_apply_apply] using multiplier_coord b (a j) ⟨v,hv j⟩ m
    rw [hc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs]
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => ht j)]
  have hs : Summable (fun m => ∑ j, if m ∈ s then 0 else |a j m|^2 * ‖b.repr v m‖^2) := by
    exact summable_sum (fun j _ => ht j)
  rw [← ht0.tsum_add hs]
  apply tsum_congr
  intro m
  split_ifs <;> simp [density]

/-- GP-13, R-2E4C2F4E: every exhausting finite-label truncation converges in
the actual common graph norm. The majorant is derived from common-domain
membership, not supplied as an independent summability premise. -/
theorem graph_core {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (hv : ∀ j, v ∈ (multiplier b (a j)).domain)
    (F : ℕ → Finset (MArr N)) (hF : ∀ m, ∀ᶠ k in atTop, m ∈ F k) :
    Tendsto (fun k => error b a v hv (F k : Set (MArr N))) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_density_iff b a v).mpr hv)
    (f := fun k m => if m ∈ F k then 0 else density b a v m)
    (g := fun _ => (0 : ℝ))
    (fun m => tendsto_const_nhds.congr' ((hF m).mono fun k hk => by simp [hk]))
    (Eventually.of_forall fun k m => by
      split_ifs <;> simp [Real.norm_eq_abs,abs_of_nonneg (density_nonneg b a v m),density_nonneg b a v m])
  simpa [graph_error_eq] using h

/-- The same proof gives a canonical finite-subset net, without choosing an
enumeration and without assuming an exhaustion. -/
theorem graph_core_net {d : ℕ} (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : HN L N) (hv : ∀ j, v ∈ (multiplier b (a j)).domain) :
    Tendsto (fun F : Finset (MArr N) => error b a v hv (F : Set (MArr N))) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_density_iff b a v).mpr hv)
    (f := fun F m => if m ∈ (F : Finset (MArr N)) then 0 else density b a v m)
    (g := fun _ => (0 : ℝ))
    (fun m => tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨{m},fun F hF => by
      have hm : m ∈ F := hF (Finset.mem_singleton_self m)
      simp [hm]⟩))
    (Eventually.of_forall fun F m => by
      split_ifs <;> simp [Real.norm_eq_abs,abs_of_nonneg (density_nonneg b a v m),density_nonneg b a v m])
  simpa [graph_error_eq] using h

/-- The graph approximants are literal finite Bethe sums. -/
theorem projection_finite_sum (b : BetheBasis L N) (F : Finset (MArr N)) (v : HN L N) :
    projection b (F : Set (MArr N)) v = ∑ m ∈ F, b.repr v m • b m := by
  have h := BetheChargeResolution.projection_hasSum b (F : Set (MArr N)) v
  have he : HasSum (fun m : (F : Set (MArr N)) => b.repr v m • b m)
      (∑ m : (F : Set (MArr N)), b.repr v m • b m) := hasSum_fintype _
  have hh := h.unique he
  rw [hh]
  exact F.sum_coe_sort (fun m => b.repr v m • b m)

end QuantumNLS.Ext025B6GraphCore

#print axioms QuantumNLS.Ext025B6GraphCore.density
#print axioms QuantumNLS.Ext025B6GraphCore.density_eq
#print axioms QuantumNLS.Ext025B6GraphCore.density_nonneg
#print axioms QuantumNLS.Ext025B6GraphCore.summable_density_iff
#print axioms QuantumNLS.Ext025B6GraphCore.projection_mem
#print axioms QuantumNLS.Ext025B6GraphCore.projection_commutes
#print axioms QuantumNLS.Ext025B6GraphCore.error
#print axioms QuantumNLS.Ext025B6GraphCore.vector_error
#print axioms QuantumNLS.Ext025B6GraphCore.graph_error_eq
#print axioms QuantumNLS.Ext025B6GraphCore.graph_core
#print axioms QuantumNLS.Ext025B6GraphCore.graph_core_net
#print axioms QuantumNLS.Ext025B6GraphCore.projection_finite_sum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6GraphCore." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Ext025B6GraphCore audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
