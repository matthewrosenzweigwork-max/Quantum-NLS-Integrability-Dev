import QuantumNLS.Ext005PhysicalInstanceR121
import QuantumNLS.Prop022WeakEquationR120

/-! Native physical competitors carry the actual moment series and physical
weak equation. The constructed cutoff limit satisfies these conditions by
proved R120 estimates; pointwise domain preservation is never substituted
for the essential uniform bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 50000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap Set Filter MeasureTheory
namespace QuantumNLS.Prop022NativeCompetitorR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005PhysicalStaticR121
open Ext005PhysicalSourceR121 Ext005PhysicalInstanceR121 Ext005SourceIntervalR32b
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005PhysicalNumberFormR114
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022CutoffLimitR120 Prop022WeakEquationR120
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)
local instance (j : ℕ) : InnerProductSpace ℝ (FormDomain (momentPositive (L := L) j)) :=
  InnerProductSpace.rclikeToReal ℂ _

lemma native_energy_to_source (j : ℕ) (I : Set ℝ) (x : ℝ → Fock L)
    (h : Ext005MomentEnergyR108.EnergyBounded j I x) :
    Ext005HilbertEnergyR112.EnergyBounded
      ((Ext005OperatorFormR113.inclusion (momentPositive (L := L) j)).restrictScalars ℝ) I x := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, hb.mono ?_⟩
  intro t ht
  obtain ⟨u, hu⟩ := (moment_form_domain_iff j (x t)).mpr ht.1
  refine ⟨u, hu, ?_⟩
  have hn := moment_form_norm_sq j u
  change ‖u‖ ^ 2 = energy j (Ext005OperatorFormR113.inclusion (momentPositive (L := L) j) u) at hn
  rw [hu] at hn
  have hh := ht.2
  nlinarith [Real.sq_sqrt hC, norm_nonneg u, Real.sqrt_nonneg C]

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "q" => (fun t => quadraticContinuous
  (numberCoefficient B (profile B M A hA hB hs u₀ t))
  (pairCoefficient B (profile B M A hA hB hs u₀ t)))

structure Competitor (j : ℕ) (l r : ℝ) (x : ℝ → Fock L) : Prop where
  continuous : ContinuousOn x (Icc l r)
  moments : Ext005MomentEnergyR108.EnergyBounded j (Icc l r) x
  weak : ∀ (w : Fock L) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p →
    tsupport p ⊆ Ioo l r →
      (∫ t, deriv p t * (⟪embedding (L := L) 1 w, x t⟫_ℂ).re) =
        -(∫ t, p t * (q t (rootLift 1 (x t)) w).im)

lemma Competitor.source_D3 (hM : 0 ≤ M) (j : ℕ) (hj : 1 ≤ j)
    (l r : ℝ) (x : ℝ → Fock L)
    (hx : Competitor B M A hA hB hs u₀ j l r x) :
    D3On (momentPositive (L := L) j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) x := by
  refine ⟨hx.continuous, native_energy_to_source j (Icc l r) x hx.moments, ?_⟩
  intro v p hp hc hsupp
  have hh := hx.weak (firstRoot j hj v) p hp hc hsupp
  rw [firstRoot_embedding] at hh
  rw [hh]
  congr 1
  apply integral_congr_ae
  obtain ⟨C, hC, hb⟩ := hx.moments
  have hglobal := (ae_restrict_iff' measurableSet_Icc).mp hb
  filter_upwards [hglobal] with t ht
  by_cases hpt : p t = 0
  · simp only [hpt, zero_mul]
  · have hsupport : t ∈ tsupport p := by
      by_contra hn
      exact hpt (image_eq_zero_of_notMem_tsupport hn)
    have hmem : t ∈ Icc l r := Ioo_subset_Icc_self (hsupp hsupport)
    obtain ⟨u, hu⟩ := (moment_form_domain_iff j (x t)).mpr (ht hmem).1
    have hl : Ext005HilbertEnergyR112.lift
        ((Ext005OperatorFormR113.inclusion (momentPositive (L := L) j)).restrictScalars ℝ) (x t) = u := by
      rw [← hu]
      exact Ext005HilbertEnergyR112.lift_eq
        ((Ext005OperatorFormR113.inclusion (momentPositive (L := L) j)).restrictScalars ℝ)
        (Ext005OperatorFormR113.inclusion_injective (momentPositive (L := L) j)) u
    have hr : rootLift 1 (x t) = firstRoot j hj u := by
      rw [← hu, rootLift_eq 1 _ (domain_mono hj (inclusion_mem_root j u))]
      rfl
    change p t * (q t (rootLift 1 (x t)) (firstRoot j hj v)).im =
      p t * (q t (firstRoot j hj (Ext005HilbertEnergyR112.lift _ (x t))) (firstRoot j hj v)).im
    have hleft := congrArg (fun w : Fock L => p t * (q t w (firstRoot j hj v)).im) hr
    have hright := congrArg
      (fun w : FormDomain (momentPositive (L := L) j) =>
        p t * (q t (firstRoot j hj w) (firstRoot j hj v)).im) hl
    exact hleft.trans hright.symm

/-- A native record for the actual cutoff limit, with its estimates proved. -/
theorem actual_limit_competitor (hM : 0 ≤ M) (s : ℝ)
    (x : momentDomain (L := L) 3) (j : ℕ) (hj : 1 ≤ j)
    (hxj : x.val ∈ momentDomain (L := L) j) (T : ℝ) (hT : 0 ≤ T) :
    Competitor B M A hA hB hs u₀ j (s-T) (s+T)
      (limit B M A hM hA hB hs u₀ s x) where
  continuous := (limit_continuous B M A hM hA hB hs u₀ s x).continuousOn
  moments := limit_energyBounded B M A hM hA hB hs u₀ s T x j hj hxj
  weak w p hp hc hsup := common_scalar_weak B M A hM hA hB hs u₀ s x T hT w p hp hc hsup

/-- Physical uniqueness invokes the newly constructed EXT-005 instance.
The actual cutoff limit's energy bound is proved, and every competitor
belongs to the native energy-bounded weak class on this whole interval. -/
theorem PROP022_energy_weak_unique_R121 (hM : 0 ≤ M) (s : ℝ)
    (x : momentDomain (L := L) 3) (j : ℕ) (hj : 1 ≤ j)
    (hxj : x.val ∈ momentDomain (L := L) j) (T : ℝ) (hT : 0 < T)
    (y : ℝ → Fock L)
    (hy : Competitor B M A hA hB hs u₀ j (s-T) (s+T) y) (hi : y s = x.val) :
    ∀ t ∈ Icc (s-T) (s+T), y t = limit B M A hM hA hB hs u₀ s x t := by
  obtain ⟨v, _, _, _, _, _, _, hu⟩ := EXT005_physical_instance_R121
    B M A hM hA hB hs u₀ j hj (s-T) (s+T) (by linarith) s
    (by constructor <;> linarith) x.val hxj
  have hy' := Competitor.source_D3 B M A hA hB hs u₀ hM j hj _ _ y hy
  have hx' := Competitor.source_D3 B M A hA hB hs u₀ hM j hj _ _ _
    (actual_limit_competitor B M A hA hB hs u₀ hM s x j hj hxj T hT.le)
  have hyv := hu y hy' hi
  have hxv := hu _ hx' (limit_initial B M A hM hA hB hs u₀ s x)
  intro t ht
  exact (hyv t ht).trans (hxv t ht).symm

/-- Native D3 uniqueness for all finite positive and negative times. -/
theorem PROP022_all_finite_times_unique_R121 (hM : 0 ≤ M) (s : ℝ)
    (x : momentDomain (L := L) 3) (j : ℕ) (hj : 1 ≤ j)
    (hxj : x.val ∈ momentDomain (L := L) j) (y : ℝ → Fock L)
    (hy : ∀ T : ℝ, 0 < T → Competitor B M A hA hB hs u₀ j (s-T) (s+T) y)
    (hi : y s = x.val) : y = limit B M A hM hA hB hs u₀ s x := by
  funext t
  let T := |t-s| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  apply PROP022_energy_weak_unique_R121 B M A hA hB hs u₀ hM s x j hj hxj T hT y (hy T hT) hi t
  constructor <;> dsimp [T] <;> linarith [le_abs_self (t-s), neg_abs_le (t-s)]

/-- The zero-sector part of PROP-022 assembled through the physical instance:
all fixed positive integer moments, native weak records, norm conservation,
and D3 uniqueness. The unitary/implementation/BD-02 clauses remain separate. -/
theorem PROP022_zero_sector_R121 (hM : 0 ≤ M) (s : ℝ) (v : HN L 0)
    (T : ℝ) (hT : 0 < T) :
    let z := zeroSectorLimit B M A hM hA hB hs u₀ s v
    Continuous z ∧ (∀ t, ‖z t‖ = ‖v‖) ∧
      (∀ j : ℕ, 1 ≤ j → Competitor B M A hA hB hs u₀ j (s-T) (s+T) z) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ y : ℝ → Fock L,
        Competitor B M A hA hB hs u₀ j (s-T) (s+T) y →
        y s = Ext025B3PhysicalSectors.inclusion L 0 v →
          ∀ t ∈ Icc (s-T) (s+T), y t = z t := by
  dsimp only
  let x : momentDomain (L := L) 3 :=
    ⟨Ext025B3PhysicalSectors.inclusion L 0 v, (vacuum_sector_energy 3 v).1⟩
  refine ⟨limit_continuous B M A hM hA hB hs u₀ s x,
    zeroSectorLimit_norm B M A hM hA hB hs u₀ s v, ?_, ?_⟩
  · intro j hj
    exact actual_limit_competitor B M A hA hB hs u₀ hM s x j hj
      (vacuum_sector_energy j v).1 T hT.le
  · intro j hj y hy hi
    exact PROP022_energy_weak_unique_R121 B M A hA hB hs u₀ hM s x j hj
      (vacuum_sector_energy j v).1 T hT y hy hi

end QuantumNLS.Prop022NativeCompetitorR121
#print axioms QuantumNLS.Prop022NativeCompetitorR121.PROP022_all_finite_times_unique_R121
#print axioms QuantumNLS.Prop022NativeCompetitorR121.PROP022_zero_sector_R121
#print axioms QuantumNLS.Prop022NativeCompetitorR121.actual_limit_competitor
#print axioms QuantumNLS.Prop022NativeCompetitorR121.PROP022_energy_weak_unique_R121

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022NativeCompetitorR121." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022NativeCompetitorR121." then
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
  Lean.logInfo m!"R121 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
