import QuantumNLS.Ext005HilbertUniqueR112

/-! R112: native energy-bounded weak-solution uniqueness on an arbitrary
Hilbert form-domain embedding, on closed intervals and the source [0,1).
There is no hypothesis on values at time 1 or outside the source interval. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005HilbertD3R112
open Ext005IntervalChainR111 Ext005HilbertChainR112 Ext005HilbertEnergyR112
open Ext005HilbertUniqueR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Native D3 uniqueness for a bounded skew form in real Riesz coordinates.
The form space is arbitrary, rather than the physical sector model. -/
theorem energy_unique_on (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b : ℝ) (_hab : a < b)
    (x y : ℝ → H) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hex : EnergyBounded i (Icc a b) x) (hey : EnergyBounded i (Icc a b) y)
    (hK : AEStronglyMeasurable K (volume.restrict (Icc a b)))
    (hKb : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t, t ∈ Icc a b → ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Icc a b → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hwx : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t))
      (fun t => K t (lift i (x t))))
    (hwy : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (y t))
      (fun t => K t (lift i (y t))))
    (hinit : x a = y a) : ∀ t ∈ Icc a b, x t = y t := by
  let u := (Icc a b).indicator (fun t => lift i (x t))
  let v := (Icc a b).indicator (fun t => lift i (y t))
  let K' := (Icc a b).indicator K
  obtain ⟨hu, E, hE, hbu⟩ := energy_coordinates i hinj (Icc a b) measurableSet_Icc x
    (hx.aestronglyMeasurable measurableSet_Icc) hex
  obtain ⟨hv, F, hF, hbv⟩ := energy_coordinates i hinj (Icc a b) measurableSet_Icc y
    (hy.aestronglyMeasurable measurableSet_Icc) hey
  have hK' : AEStronglyMeasurable K' volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hK
  obtain ⟨M, hM, hbm⟩ := hKb
  have hwe (z : ℝ → H)
      (hz : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (z t))
        (fun t => K t (lift i (z t)))) :
      WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (z t))
        (fun t => K' t ((Icc a b).indicator (fun s => lift i (z s)) t)) := by
    apply weak_congr hz (fun _ _ => rfl)
    intro t ht
    simp only [K', indicator_of_mem (Ioo_subset_Icc_self ht)]
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | hat
  · simpa only [← heq] using hinit
  · have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hwsub : Ioo a t ⊆ Ioo a b := fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩
    apply coordinate_equal_endpoints i hinj hdense a t hat x y u v K'
      (hx.mono hsub) (hy.mono hsub) hu hv hK'
      (hbu.mono fun s hs hsI => (hs (hsub hsI)).1)
      (hbv.mono fun s hs hsI => (hs (hsub hsI)).1) E F M hE hF hM
    · filter_upwards [hbu, hbv, hbm] with s hs hs' hsM hsI
      exact ⟨(hs (hsub hsI)).2, (hs' (hsub hsI)).2,
        by simpa only [K', indicator_of_mem (hsub hsI)] using hsM (hsub hsI)⟩
    · filter_upwards [hskew] with s hs hsI
      simpa only [K', indicator_of_mem (hsub hsI)] using hs (hsub hsI)
    · exact weak_mono (hwe x hwx) hwsub
    · exact weak_mono (hwe y hwy) hwsub
    · exact hinit

/-- Intrinsic Hilbert form-domain D3 uniqueness on the literal source interval.
Only local essential form and coefficient bounds are required. -/
theorem energy_unique_source_interval (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (x y : ℝ → H) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Ico 0 1)) (hy : ContinuousOn y (Ico 0 1))
    (hex : ∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) x)
    (hey : ∀ T ∈ Ioo (0 : ℝ) 1, EnergyBounded i (Icc 0 T) y)
    (hK : AEStronglyMeasurable K (volume.restrict (Ico 0 1)))
    (hKb : ∀ T ∈ Ioo (0 : ℝ) 1, ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ t, t ∈ Icc 0 T → ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Ico (0 : ℝ) 1 → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hwx : WeakDerivativeOn (Ioo 0 1) (fun t => i.adjoint (x t))
      (fun t => K t (lift i (x t))))
    (hwy : WeakDerivativeOn (Ioo 0 1) (fun t => i.adjoint (y t))
      (fun t => K t (lift i (y t))))
    (hinit : x 0 = y 0) : ∀ t ∈ Ico (0 : ℝ) 1, x t = y t := by
  intro t ht
  let T := (t + 1) / 2
  have hT : T ∈ Ioo (0 : ℝ) 1 := by dsimp [T]; constructor <;> linarith [ht.1, ht.2]
  have hsub : Icc (0 : ℝ) T ⊆ Ico 0 1 := fun s hs => ⟨hs.1, hs.2.trans_lt hT.2⟩
  have hws : Ioo (0 : ℝ) T ⊆ Ioo 0 1 := fun s hs => ⟨hs.1, hs.2.trans hT.2⟩
  exact energy_unique_on i hinj hdense 0 T hT.1 x y K (hx.mono hsub) (hy.mono hsub)
    (hex T hT) (hey T hT) (hK.mono_measure (Measure.restrict_mono_set volume hsub))
    (hKb T hT) (hskew.mono fun s hs hsI => hs (hsub hsI))
    (weak_mono hwx hws) (weak_mono hwy hws) hinit t ⟨ht.1, by dsimp [T]; linarith [ht.2]⟩

end QuantumNLS.Ext005HilbertD3R112
#print axioms QuantumNLS.Ext005HilbertD3R112.energy_unique_on
#print axioms QuantumNLS.Ext005HilbertD3R112.energy_unique_source_interval

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005HilbertD3R112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005HilbertD3R112." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
