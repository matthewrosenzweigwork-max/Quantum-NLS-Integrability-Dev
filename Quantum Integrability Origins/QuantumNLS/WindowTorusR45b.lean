import QuantumNLS.WindowPhaseR44b
import QuantumNLS.ActionTorus

/-! Compact unions of full weighted modulus tori, including all coordinate zeros.
The initial compact set is fixed before any cutoff or times are selected. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
namespace QuantumNLS.WindowTorusR45b

def act (W : PosWeight) (θ : ℤ → Circle) (z : WSeq W) : WSeq W :=
  (toL2ᵢ W).symm (ActionTorus.rotate θ (toL2ᵢ W z))

@[simp] theorem act_val (W : PosWeight) (θ : ℤ → Circle) (z : WSeq W) (j : ℤ) :
    (act W θ z).val j = (θ j : ℂ)*z.val j := by
  have he := congrArg (fun v : lp (fun _ : ℤ => ℂ) 2 => v j)
    ((toL2ᵢ W).apply_symm_apply (ActionTorus.rotate θ (toL2ᵢ W z)))
  change (Real.sqrt (W.w j) : ℂ)*(act W θ z).val j =
    (θ j : ℂ)*((Real.sqrt (W.w j) : ℂ)*z.val j) at he
  apply mul_left_cancel₀ (sqrt_ne_zero' W j)
  rw [he]
  ring

theorem continuous_act (W : PosWeight) :
    Continuous (fun p : (ℤ → Circle) × WSeq W => act W p.1 p.2) :=
  (toL2ᵢ W).symm.continuous.comp (ActionTorus.continuous_rotate.comp
    (continuous_fst.prodMk ((toL2ᵢ W).continuous.comp continuous_snd)))

theorem norm_act (W : PosWeight) (θ : ℤ → Circle) (z : WSeq W) :
    ‖act W θ z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_tsum,norm_sq_eq_tsum]
  simp

def hull (W : PosWeight) (K : Set (WSeq W)) : Set (WSeq W) :=
  (fun p : (ℤ → Circle) × WSeq W => act W p.1 p.2) '' (univ ×ˢ K)

theorem isCompact_hull (W : PosWeight) {K : Set (WSeq W)} (hK : IsCompact K) :
    IsCompact (hull W K) :=
  (isCompact_univ.prod hK).image (continuous_act W)

theorem rotate_mem_hull (W : PosWeight) {K : Set (WSeq W)} {z : WSeq W}
    (hz : z ∈ K) (α : ℤ → ℝ) : WindowPhaseR44b.rotate α z ∈ hull W K := by
  refine ⟨(fun j => Circle.exp (α j),z),⟨mem_univ _,hz⟩,?_⟩
  apply WSeq.ext
  funext j
  simp

/-- Every equal-modulus point belongs to the full torus, with no division at zero. -/
theorem moduli_mem_hull (W : PosWeight) {K : Set (WSeq W)} {x z : WSeq W}
    (hz : z ∈ K) (hm : ∀ j, ‖x.val j‖ = ‖z.val j‖) : x ∈ hull W K := by
  classical
  have hex : ∀ j, ∃ θ : Circle, (θ : ℂ)*z.val j = x.val j := by
    intro j
    by_cases hj : z.val j = 0
    · have hx : x.val j = 0 := norm_eq_zero.mp (by rw [hm j,hj,norm_zero])
      exact ⟨1,by simp [hj,hx]⟩
    · have hn : ‖x.val j / z.val j‖ = 1 := by
        rw [norm_div,hm j,div_self (norm_ne_zero_iff.mpr hj)]
      exact ⟨⟨x.val j / z.val j,mem_sphere_zero_iff_norm.mpr hn⟩,div_mul_cancel₀ _ hj⟩
  choose θ hθ using hex
  refine ⟨(θ,z),⟨mem_univ _,hz⟩,?_⟩
  apply WSeq.ext
  funext j
  exact (act_val W θ z j).trans (hθ j)

theorem bound_hull (W : PosWeight) {K : Set (WSeq W)} {B : ℝ}
    (hB : ∀ z ∈ K, ‖z‖ ≤ B) : ∀ z ∈ hull W K, ‖z‖ ≤ B := by
  rintro z ⟨⟨θ,x⟩,hx,rfl⟩
  exact (norm_act W θ x).le.trans (hB x hx.2)

end QuantumNLS.WindowTorusR45b
#print axioms QuantumNLS.WindowTorusR45b.isCompact_hull
#print axioms QuantumNLS.WindowTorusR45b.moduli_mem_hull

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowTorusR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowTorusR45b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
