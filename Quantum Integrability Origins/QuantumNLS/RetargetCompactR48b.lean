import QuantumNLS.DynSeedR47b
import QuantumNLS.R52CFCompact
import QuantumNLS.Ext025A3Fields
import QuantumNLS.HighAngleRotations

/-! ROOT-01 applied to the bounded physical profile class used by R-D51987CA,
and compactness of its entire orbit in the actual chart. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section

namespace QuantumNLS.RetargetCompactR48b

open Set Filter Topology
open PhysicalTensor Sobolev CountRotations DynSeedInputR47b DynSeedClassicalR47b
open D01LocalPrimitive (K)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The same tested profile class lifted to the accepted DEF-002 physical H¹ space. -/
def liftedProfiles (R : ℝ) : Set (H02 L 1) :=
  {x | x.val ∈ R52CFCompact.profileClass L R}

theorem liftedProfiles_bounded (R : ℝ) : Bornology.IsBounded (liftedProfiles (L := L) R) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨|R|, ?_⟩
  intro u hu
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [H02.norm_sq_eq, sq_abs]
  exact hu.2.2

theorem profile_image (R : ℝ) :
    (H02.toL2 (L := L) (s := 0) (by norm_num)).comp
      (H02.mono (L := L) (s := 0) (t := 1) (by norm_num)) '' liftedProfiles R =
    R52CFCompact.profileClass L R := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hu
    have hs : Fourier.MemHs L 1 (fun n => Fourier.fourierL2 L u n) := by
      obtain ⟨f, hf, rfl⟩ := hu.1
      exact R52CFCompact.memHs_smooth hf
    exact ⟨WField.mk (W := def002 L 1) u hs, hu, rfl⟩

/-- The strict ROOT-01 exponent gap is 1 > 0, with the DEF-002 weight. -/
theorem root01_profile_compact (R : ℝ) : IsCompact (closure (R52CFCompact.profileClass L R)) := by
  let A := H02.toL2 (L := L) (s := 0) (by norm_num)
  let J := H02.mono (L := L) (s := 0) (t := 1) (by norm_num)
  have hc : IsCompact (closure (J '' liftedProfiles R)) :=
    Ext025A3.root01_def002_precompact (by norm_num) (by norm_num) (liftedProfiles_bounded R)
  have hclosed : IsClosed (A '' closure (J '' liftedProfiles R)) :=
    (hc.image A.continuous).isClosed
  apply (hc.image A.continuous).of_isClosed_subset isClosed_closure
  apply closure_minimal _ hclosed
  rw [← profile_image R]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨J x, subset_closure ⟨x, hx, rfl⟩, rfl⟩

theorem profile_closure_unit (R : ℝ) {u : L2T L}
    (hu : u ∈ closure (R52CFCompact.profileClass L R)) : ‖u‖ = 1 := by
  have hclosed : IsClosed {v : L2T L | ‖v‖ = 1} := isClosed_eq continuous_norm continuous_const
  exact closure_minimal (fun _ hv => hv.2.1) hclosed hu

theorem continuous_physicalAngle (hκ : 0 < κ) :
    Continuous (fun p : AngleTorus × L2T L => physicalAngle hκ p.1 p.2) := by
  let C := Def021ChartR41b.chart L κ hκ
  have hc : Continuous C.Φ := continuous_iff_continuousAt.mpr fun u => (C.analytic u).continuousAt
  have hd : Continuous C.Ψ :=
    continuous_iff_continuousAt.mpr fun z => (C.inverse_analytic z).continuousAt
  exact hd.comp (ActionTorus.continuous_rotate.comp
    ((continuous_fst.inv).prodMk (hc.comp continuous_snd)))

/-- The union of full coordinate orbits over the physical L² closure of the smooth ball. -/
def orbit (hκ : 0 < κ) (R : ℝ) : SubMulAction Circle (L2T L) where
  carrier := {v | ∃ u ∈ closure (R52CFCompact.profileClass L R), v ∈ torus hκ u}
  smul_mem' c v hv := by
    obtain ⟨u, hu, hv⟩ := hv
    exact ⟨u, hu, (torus hκ u).smul_mem c hv⟩

theorem orbit_eq_image (hκ : 0 < κ) (R : ℝ) :
    (orbit (L := L) hκ R : Set (L2T L)) =
      (fun p : AngleTorus × L2T L => physicalAngle hκ p.1 p.2) ''
        (univ ×ˢ closure (R52CFCompact.profileClass L R)) := by
  let C := Def021ChartR41b.chart L κ hκ
  ext v
  constructor
  · rintro ⟨u, hu, hv⟩
    change ∀ j, ‖C.Φ v j‖ = ‖C.Φ u j‖ at hv
    have hpoint (j : ℤ) : ∃ z : Circle, (z : ℂ) * C.Φ u j = C.Φ v j := by
      by_cases hj : C.Φ u j = 0
      · have hz : C.Φ v j = 0 := norm_eq_zero.mp (by simpa only [hj, norm_zero] using hv j)
        exact ⟨1, by simp [hj, hz]⟩
      · have hnorm : ‖C.Φ v j / C.Φ u j‖ = 1 := by
          rw [norm_div, hv j, div_self (norm_ne_zero_iff.mpr hj)]
        exact ⟨⟨C.Φ v j / C.Φ u j, mem_sphere_zero_iff_norm.mpr hnorm⟩,
          div_mul_cancel₀ _ hj⟩
    choose z hz using hpoint
    let θ : AngleTorus := fun j => (z j)⁻¹
    refine ⟨(θ, u), ⟨mem_univ _, hu⟩, ?_⟩
    change C.Ψ (coordinateRotation θ (C.Φ u)) = v
    rw [← C.left_inverse v]
    congr 1
    apply lp.ext
    funext j
    change (((z j)⁻¹)⁻¹ : Circle).val * C.Φ u j = C.Φ v j
    rw [inv_inv]
    exact hz j
  · rintro ⟨⟨θ, u⟩, ⟨_, hu⟩, rfl⟩
    exact ⟨u, hu, angle_mem_torus hκ u u (fun _ => rfl) θ⟩

theorem orbit_compact (hκ : 0 < κ) (R : ℝ) :
    IsCompact (orbit (L := L) hκ R : Set (L2T L)) := by
  rw [orbit_eq_image]
  exact (isCompact_univ.prod (root01_profile_compact R)).image (continuous_physicalAngle hκ)

theorem orbit_unit (hκ : 0 < κ) (R : ℝ) {v : L2T L} (hv : v ∈ orbit hκ R) : ‖v‖ = 1 := by
  obtain ⟨u, hu, hv⟩ := hv
  exact (torus_norm hκ hv).trans (profile_closure_unit R hu)

theorem orbit_approximants (hκ : 0 < κ) (R : ℝ) (a b : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : L2T L → ℂ, DynSeedApproxR47b.Coherent f ∧
      ∀ v ∈ orbit hκ R, ‖f v - symbol hκ a b v‖ < ε := by
  let O := orbit (L := L) hκ R
  let c : C(O, ℂ) := ⟨fun v => symbol hκ a b v.val,
    (symbol_continuous hκ a b).comp continuous_subtype_val⟩
  obtain ⟨f, hf, he⟩ := DynSeedApproxR47b.dense_coherent O (orbit_compact hκ R) c
    (fun g v => symbol_phase hκ a b g v.val) hε
  exact ⟨f, hf, fun v hv => he ⟨v, hv⟩⟩

end QuantumNLS.RetargetCompactR48b

#print axioms QuantumNLS.RetargetCompactR48b.root01_profile_compact
#print axioms QuantumNLS.RetargetCompactR48b.orbit_compact
#print axioms QuantumNLS.RetargetCompactR48b.orbit_approximants

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetCompactR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetCompactR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
