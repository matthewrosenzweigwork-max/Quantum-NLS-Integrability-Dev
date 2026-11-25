import QuantumNLS.WindowScalarsR45b
import QuantumNLS.WindowTrajectoryR45b

/-! Actual contour trajectories in coordinates and their actual physical
inverse images. The real coordinate Hamilton equation and conservation of
every indexed physical action are proved, with a unique coordinate path.
The physical Hamiltonian-field transfer is a distinct remaining obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowScalarsR45b QuantumNLS.WindowTrajectoryR45b
open QuantumNLS.WindowPhaseR44b QuantumNLS.WindowRadialR45b
open QuantumNLS.WindowActualEstimatesR44b QuantumNLS.Reg015Setting
namespace QuantumNLS.WindowActualTrajectoryR45b
variable {L κ : ℝ} [Fact (0 < L)]

/-- Strong continuity follows from the continuous full product-torus action. -/
theorem trajectory_continuous {W : PosWeight} (F : WSeq W → ℝ) (z : WSeq W) :
    Continuous (trajectory F z) := by
  have hα : Continuous (fun t : ℝ => fun j : ℤ => Circle.exp (-t*frequency F z j)) :=
    continuous_pi fun j => Circle.exp.continuous.comp (continuous_neg.mul continuous_const)
  have hp : Continuous (fun t : ℝ => WindowTorusR45b.act W (fun j => Circle.exp (-t*frequency F z j)) z) :=
    (WindowTorusR45b.continuous_act W).comp
      (hα.prodMk (continuous_const : Continuous (fun _ : ℝ => z)))
  have he : (fun t : ℝ => WindowTorusR45b.act W (fun j => Circle.exp (-t*frequency F z j)) z) =
      trajectory F z := by
    funext t
    apply WSeq.ext
    funext j
    simp only [WindowTorusR45b.act_val,trajectory,rotate_val]
  rwa [he] at hp

/-- Local differentiability on the full initial torus suffices for uniqueness;
no differentiability away from that torus is needed for a fixed cutoff. -/
theorem unique_on_torus {W : PosWeight} {F : WSeq W → ℝ} {γ : ℝ → WSeq W}
    (hd : ∀ α, DifferentiableAt ℝ F (rotate α (γ 0)))
    (hi : ∀ α y, F (rotate α y) = F y) (hγ : IsHamiltonianPath F γ) (t : ℝ) :
    γ t = trajectory F (γ 0) t := by
  have hdγ : ∀ τ, DifferentiableAt ℝ F (γ τ) := by
    intro τ
    obtain ⟨α,he⟩ := exists_rotate (fun j => (path_moduli hγ τ j).symm)
    rw [he]
    exact hd α
  apply WSeq.ext
  funext j
  have hf : ∀ τ, frequency F (γ τ) j = frequency F (γ 0) j := fun τ =>
    frequency_of_moduli (hdγ 0) (hdγ τ) hi (fun n => (path_moduli hγ τ n).symm) j
  have hc : ∀ τ, HasDerivAt (fun x => (γ x).val j)
      (-Complex.I*(frequency F (γ 0) j : ℂ)*(γ τ).val j) τ := by
    intro τ
    simpa only [hf τ] using hγ τ j
  exact scalar_unique _ _ hc t

/-- For sufficiently large fixed cutoffs, the literal contour's scalar
derivative determines the unique coordinate Hamiltonian trajectory on every
torus through the fixed compact initial class. -/
theorem window_coordinate_flow (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (hr : r ≤ d) {h : ℝ} (hh : 0 < h)
    {K : Set (h02 L (sequenceOrder d))} (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ z ∈ K,
      IsHamiltonianPath (window hκ C d r h l) (trajectory (window hκ C d r h l) z) ∧
      ∀ γ : ℝ → h02 L (sequenceOrder d), γ 0 = z →
        IsHamiltonianPath (window hκ C d r h l) γ →
        ∀ t, γ t = trajectory (window hκ C d r h l) z t := by
  have hH := WindowTorusR45b.isCompact_hull (def002 L (sequenceOrder d)) hK
  obtain ⟨A,hA,l0,hdata⟩ := scalar_data hκ C d r hr hh hH
  refine ⟨l0,?_⟩
  intro l hl z hz
  have hd : ∀ α, DifferentiableAt ℝ (window hκ C d r h l) (rotate α z) :=
    fun α => (hdata l hl _ (WindowTorusR45b.rotate_mem_hull _ hz α)).1
  refine ⟨trajectory_hamiltonian z hd (window_rotation hκ C d r h l),?_⟩
  intro γ hγ0 hγ t
  have hd' : ∀ α, DifferentiableAt ℝ (window hκ C d r h l) (rotate α (γ 0)) := by
    simpa only [hγ0] using hd
  simpa only [hγ0] using unique_on_torus hd' (window_rotation hκ C d r h l) hγ t

def physicalPath (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) (t : ℝ) : PhysicalTensor.L2T L :=
  C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 (trajectory (window hκ C d r h l) z t))

theorem physicalPath_continuous (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) :
    Continuous (physicalPath hκ C d r h l z) :=
  (continuous_iff_continuousAt.mpr fun x => (C.inverse_analytic x).continuousAt).comp
    ((toBase (sequenceOrder d) (sequenceOrder d).2).continuous.comp
      (trajectory_continuous (window hκ C d r h l) z))

theorem physicalPath_chart (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) (t : ℝ) :
    C.Φ (physicalPath hκ C d r h l z t) =
      toBase (sequenceOrder d) (sequenceOrder d).2 (trajectory (window hκ C d r h l) z t) :=
  C.right_inverse _

/-- Literal indexed physical actions are preserved, by exact chart moduli. -/
theorem physicalPath_actions (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (d r : ℕ) (h : ℝ) (l : ℕ) (z : h02 L (sequenceOrder d)) (t : ℝ) (j : ℤ) :
    (RootIndexedMasses.masses hκ (physicalPath hκ C d r h l z t)).1 j =
      (RootIndexedMasses.masses hκ (C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z))).1 j := by
  have hc₁ : C.Φ (physicalPath hκ C d r h l z t) j =
      (trajectory (window hκ C d r h l) z t).val j :=
    (congrArg (fun x : D01LocalPrimitive.K => x j)
      (physicalPath_chart hκ C d r h l z t)).trans
      (toBase_apply (sequenceOrder d) (sequenceOrder d).2 _ j)
  have hc₂ : C.Φ (C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z)) j = z.val j :=
    (congrArg (fun x : D01LocalPrimitive.K => x j) (C.right_inverse _)).trans
      (toBase_apply (sequenceOrder d) (sequenceOrder d).2 z j)
  calc
    _ = ‖C.Φ (physicalPath hκ C d r h l z t) j‖^2 := (C.actions _ j).symm
    _ = ‖(trajectory (window hκ C d r h l) z t).val j‖^2 := congrArg (fun x : ℂ => ‖x‖^2) hc₁
    _ = ‖z.val j‖^2 := congrArg (fun x : ℝ => x^2) (trajectory_moduli _ z t j)
    _ = ‖C.Φ (C.Ψ (toBase (sequenceOrder d) (sequenceOrder d).2 z)) j‖^2 :=
      (congrArg (fun x : ℂ => ‖x‖^2) hc₂).symm
    _ = _ := C.actions _ j

end QuantumNLS.WindowActualTrajectoryR45b
#print axioms QuantumNLS.WindowActualTrajectoryR45b.window_coordinate_flow
#print axioms QuantumNLS.WindowActualTrajectoryR45b.physicalPath_actions

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowActualTrajectoryR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowActualTrajectoryR45b." then
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
