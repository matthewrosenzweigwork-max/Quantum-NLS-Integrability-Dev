import QuantumNLS.WindowPhaseR44b
import QuantumNLS.WindowCompactInverseR44b

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: complete quantitative comparison of two diagonal rotations.
These are functional-analytic estimates, not a replacement hierarchy theorem.
The scalar-to-rotation identification is reserved for the exact hierarchy input. -/
noncomputable section
set_option autoImplicit false
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowPhaseR44b
namespace QuantumNLS.WindowRateEstimateR44b

/-- Forget the positive order without rescaling coordinates. -/
def lower (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j) (z : WSeq W) : WSeq unitWeight :=
  WSeq.mk unitWeight z.val (z.summable.of_nonneg_of_le
    (fun j => by simp [unitWeight])
    (fun j => by dsimp [unitWeight]; nlinarith [hW j,sq_nonneg ‖z.val j‖]))

@[simp] theorem lower_val (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j) (z : WSeq W) :
    (lower W hW z).val = z.val := rfl

theorem norm_lower_le (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j) (z : WSeq W) :
    ‖lower W hW z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PosWeight.norm_sq_eq_tsum,PosWeight.norm_sq_eq_tsum]
  exact (lower W hW z).summable.tsum_le_tsum
    (fun j => by
      change 1*‖z.val j‖^2 ≤ W.w j*‖z.val j‖^2
      exact mul_le_mul_of_nonneg_right (hW j) (sq_nonneg _)) z.summable

/-- The entire high-order difference is bounded by twice the INITIAL norm. -/
theorem high_difference (W : PosWeight) (z : WSeq W) (α β : ℤ → ℝ) :
    ‖rotate α z - rotate β z‖ ≤ 2*‖z‖ := by
  calc ‖rotate α z-rotate β z‖ ≤ ‖rotate α z‖+‖rotate β z‖ := norm_sub_le _ _
    _ = _ := by rw [norm_rotate,norm_rotate]; ring

/-- Reciprocal-weight gradient comparison, phase comparison and interpolation
produce exactly a^-1/4. The high norm is the fixed torus norm. -/
theorem rotation_rate (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j)
    (z : WSeq W) (α β : ℤ → ℝ) (δ : WSeq (reciprocal W))
    (hδ : ∀ j, δ.val j = (((α j-β j : ℝ) : ℂ)*z.val j))
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (herror : ‖δ‖ ≤ C*a^(-(1/2 : ℝ))) :
    ‖lower W hW (rotate α z-rotate β z)‖ ≤
      Real.sqrt (C*(2*‖z‖))*a^(-(1/4 : ℝ)) := by
  obtain ⟨e,he,hn⟩ := rotation_difference W z α β δ hδ
  exact interpolated_rate W e (rotate α z-rotate β z)
    (lower W hW (rotate α z-rotate β z)) he rfl ha hC (by positivity)
    (hn.trans herror) (high_difference W z α β)

/-- One physical inverse Lipschitz constant, chosen before the cutoff,
works for every pair in the fixed compact coordinate set. -/
theorem physical_rate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j)
    {K : Set (WSeq unitWeight)} (hK : IsCompact K)
    (f : WSeq unitWeight → G) (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : WSeq W) (α β : ℤ → ℝ)
      (δ : WSeq (reciprocal W)),
      (∀ j, δ.val j = (((α j-β j : ℝ) : ℂ)*z.val j)) →
      ∀ {a C : ℝ}, 0 < a → 0 ≤ C → ‖δ‖ ≤ C*a^(-(1/2 : ℝ)) →
      lower W hW (rotate α z) ∈ K → lower W hW (rotate β z) ∈ K →
      ‖f (lower W hW (rotate α z))-f (lower W hW (rotate β z))‖ ≤
        (M*Real.sqrt (C*(2*‖z‖)))*a^(-(1/4 : ℝ)) := by
  obtain ⟨M,hM,hb⟩ := WindowCompactInverseR44b.compact_lipschitz hK f hf
  refine ⟨M,hM,?_⟩
  intro z α β δ hδ a C ha hC herror hx hy
  have he : lower W hW (rotate α z)-lower W hW (rotate β z) =
      lower W hW (rotate α z-rotate β z) := WSeq.ext rfl
  calc ‖f (lower W hW (rotate α z))-f (lower W hW (rotate β z))‖ ≤
      M*‖lower W hW (rotate α z)-lower W hW (rotate β z)‖ := hb _ hx _ hy
    _ ≤ M*(Real.sqrt (C*(2*‖z‖))*a^(-(1/4 : ℝ))) := by
      rw [he]
      exact mul_le_mul_of_nonneg_left (rotation_rate W hW z α β δ hδ ha hC herror) hM
    _ = _ := by ring

/-- Uniformity on a fixed bounded initial class follows from the same
compact inverse constant; only the INITIAL high norm enters. -/
theorem uniform_physical_rate {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (W : PosWeight) (hW : ∀ j, 1 ≤ W.w j)
    {K : Set (WSeq unitWeight)} (hK : IsCompact K)
    (f : WSeq unitWeight → G) (hf : ContDiff ℝ 1 f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (B : ℝ) (z : WSeq W), ‖z‖ ≤ B →
      ∀ (α β : ℤ → ℝ) (δ : WSeq (reciprocal W)),
      (∀ j, δ.val j = (((α j-β j : ℝ) : ℂ)*z.val j)) →
      ∀ {a A : ℝ}, 0 < a → 0 ≤ A → ‖δ‖ ≤ A*a^(-(1/2 : ℝ)) →
      lower W hW (rotate α z) ∈ K → lower W hW (rotate β z) ∈ K →
      ‖f (lower W hW (rotate α z))-f (lower W hW (rotate β z))‖ ≤
        (M*Real.sqrt (A*(2*B)))*a^(-(1/4 : ℝ)) := by
  obtain ⟨M,hM,hb⟩ := physical_rate W hW hK f hf
  refine ⟨M,hM,?_⟩
  intro B z hz α β δ hδ a A ha hA herror hx hy
  apply (hb z α β δ hδ ha hA herror hx hy).trans
  have hs : Real.sqrt (A*(2*‖z‖)) ≤ Real.sqrt (A*(2*B)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hA)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hM)
    (Real.rpow_nonneg ha.le _)

end QuantumNLS.WindowRateEstimateR44b

#print axioms QuantumNLS.WindowRateEstimateR44b.rotation_rate
#print axioms QuantumNLS.WindowRateEstimateR44b.physical_rate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowRateEstimateR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowRateEstimateR44b." then
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
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
