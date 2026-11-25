import QuantumNLS.Ext005CommonWeakR127

/-! Cross-j compatibility of the ACCEPTED fixed-j R121 constructions.
Every uniqueness application is in its own energy-bounded D3 class, with
the comparison curve's moment bounds and physical weak equation proved.
No identification between different comparison operators is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open Set Filter ContinuousLinearMap MeasureTheory
namespace QuantumNLS.Ext005CrossJCompatibilityR127
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005SourceIntervalR32b
open Ext005PhysicalSourceR121 Ext005PhysicalInstanceR121 Ext005PatchingR32b
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Ext005PairCommutatorR108
open Prop022FockPropagatorR122 Prop022DomainR122 Prop022NativeCompetitorR121
open Ext005CommonWeakR127
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀
local notation "S" => physicalSource B M A hM hA hB hs u₀

/-- The common curve belongs to the precise physical source D3 class on
any finite signed interval. The bound is inherited by restriction from a
proved centered-interval bound, never from pointwise membership alone. -/
theorem common_D3 (j : ℕ) (hj : 1 ≤ j) (l r s : ℝ)
    (x : momentDomain (L := L) j) :
    D3On (momentPositive j) l r (S j hj l r) (fun t => V s t x.val) := by
  let T := |l-s| + |r-s| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hl : s-T ≤ l := by dsimp [T]; linarith [neg_abs_le (l-s), abs_nonneg (r-s)]
  have hr : r ≤ s+T := by dsimp [T]; linarith [le_abs_self (r-s), abs_nonneg (l-s)]
  have hc := Competitor.source_D3 B M A hA hB hs u₀ hM j hj (s-T) (s+T) _
    (common_competitor B M A hM hA hB hs u₀ j hj s T hT x)
  exact D3On_restrict (momentPositive j) (s-T) (s+T) (S j hj (s-T) (s+T))
    l r hl hr _ hc

/-- Every source D3 solution agrees with the common evolution, with its
initial datum in the FULL moment domain of the chosen j. -/
theorem solution_eq_common (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r)
    (s : ℝ) (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j)
    (y : ℝ → Fock L) (hy : D3On (momentPositive j) l r (S j hj l r) y)
    (hi : y s = x) : ∀ t ∈ Icc l r, y t = V s t x := by
  rcases eq_or_lt_of_le hlr with he | hlt
  · subst r
    have hsl : s = l := le_antisymm hs₀.2 hs₀.1
    subst s
    intro t ht
    have htl : t = l := le_antisymm ht.2 ht.1
    simpa only [htl, evolution_self] using hi
  · apply EXT005_D3_finite_interval_unique (momentPositive j) l r (S j hj l r)
      s hlt hs₀ y (fun t => V s t x) hy
      (common_D3 B M A hM hA hB hs u₀ j hj l r s ⟨x,hx⟩)
    simpa only [evolution_self] using hi

/-- Cross-j comparison for arbitrary actual D3 evolutions on their common
domain. The D3 conditions retain the essential uniform energy bounds. -/
theorem cross_j_D3 (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≤ k)
    (l r : ℝ) (hlr : l ≤ r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) k) (y z : ℝ → Fock L)
    (hy : D3On (momentPositive j) l r (S j hj l r) y)
    (hz : D3On (momentPositive k) l r (S k hk l r) z)
    (hyi : y s = x) (hzi : z s = x) : ∀ t ∈ Icc l r, y t = z t := by
  have hyc := solution_eq_common B M A hM hA hB hs u₀ j hj l r hlr s hs₀
    x (domain_mono hjk hx) y hy hyi
  have hzc := solution_eq_common B M A hM hA hB hs u₀ k hk l r hlr s hs₀ x hx z hz hzi
  intro t ht
  exact (hyc t ht).trans (hzc t ht).symm

/-- A chosen curve from the frozen R121 existence theorem, rather than a
redefinition of the j-th curve to be the common evolution. -/
def fixedLift (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r)
    (s : ℝ) (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    ℝ → FormDomain (momentPositive (L := L) j) :=
  Classical.choose (EXT005_physical_instance_R121 B M A hM hA hB hs u₀
    j hj l r hlr s hs₀ x hx)

def fixedCurve (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r)
    (s : ℝ) (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    ℝ → Fock L :=
  fun t => Ext005OperatorFormR113.inclusion (momentPositive j)
    (fixedLift B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx t)

lemma fixedCurve_initial (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r)
    (s : ℝ) (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    fixedCurve B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx s = x :=
  (Classical.choose_spec (EXT005_physical_instance_R121 B M A hM hA hB hs u₀
    j hj l r hlr s hs₀ x hx)).1

lemma fixedCurve_D3 (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r)
    (s : ℝ) (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    D3On (momentPositive j) l r (S j hj l r)
      (fixedCurve B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx) :=
  (Classical.choose_spec (EXT005_physical_instance_R121 B M A hM hA hB hs u₀
    j hj l r hlr s hs₀ x hx)).2.2.2.2.1

/-- The specific evolutions chosen from R121 agree on Q((Num+1)^k). -/
theorem EXT005_cross_j_R127 (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≤ k)
    (l r : ℝ) (hlr : l ≤ r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) k) :
    ∀ t ∈ Icc l r,
      fixedCurve B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x (domain_mono hjk hx) t =
      fixedCurve B M A hM hA hB hs u₀ k hk l r hlr s hs₀ x hx t :=
  cross_j_D3 B M A hM hA hB hs u₀ j k hj hk hjk l r hlr s hs₀ x hx _ _
    (fixedCurve_D3 B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x (domain_mono hjk hx))
    (fixedCurve_D3 B M A hM hA hB hs u₀ k hk l r hlr s hs₀ x hx)
    (fixedCurve_initial B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x (domain_mono hjk hx))
    (fixedCurve_initial B M A hM hA hB hs u₀ k hk l r hlr s hs₀ x hx)

/-- ONE evolution, fixed before j is chosen, preserving every positive
number-moment domain. Its energy bounds, source weak equation, and
identification with every R121 construction are conclusions. -/
theorem EXT005_single_evolution_R127 :
    ∃ U : ℝ → ℝ → Fock L →ₗᵢ[ℂ] Fock L,
      (∀ s x, U s s x = x) ∧
      (∀ r s t x, U s t (U r s x) = U r t x) ∧
      (∀ s x, Continuous (fun t => U s t x)) ∧
      (∀ s t x, ‖U s t x‖ = ‖x‖) ∧
      (∀ (j : ℕ) (_hj : 1 ≤ j) (s t : ℝ) (x : momentDomain (L := L) j),
        U s t x.val ∈ momentDomain (L := L) j ∧
        energy j (U s t x.val) ≤ energy j x.val *
          Real.exp (differenceConstant j*(M*pairMajorant A)*|t-s|)) ∧
      (∀ (j : ℕ) (hj : 1 ≤ j) (l r s : ℝ) (x : momentDomain (L := L) j),
        D3On (momentPositive j) l r (S j hj l r) (fun t => U s t x.val)) ∧
      (∀ (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) (hlr : l ≤ r) (s : ℝ)
        (hs₀ : s ∈ Icc l r) (x : Fock L) (hx : x ∈ momentDomain (L := L) j),
        ∀ t ∈ Icc l r,
          fixedCurve B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx t = U s t x) ∧
      (∀ (s t : ℝ) (x : Fock L), (∀ j : ℕ, 1 ≤ j → x ∈ momentDomain (L := L) j) →
        ∀ j : ℕ, 1 ≤ j → U s t x ∈ momentDomain (L := L) j) := by
  refine ⟨V, evolution_self B M A hM hA hB hs u₀,
    evolution_comp B M A hM hA hB hs u₀,
    evolution_continuous B M A hM hA hB hs u₀,
    (fun s t x => (V s t).norm_map x),
    evolution_energy B M A hM hA hB hs u₀,
    common_D3 B M A hM hA hB hs u₀, ?_, ?_⟩
  · intro j hj l r hlr s hs₀ x hx
    exact solution_eq_common B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx _
      (fixedCurve_D3 B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx)
      (fixedCurve_initial B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx)
  · intro s t x hx j hj
    exact (evolution_energy B M A hM hA hB hs u₀ j hj s t ⟨x,hx j hj⟩).1

end QuantumNLS.Ext005CrossJCompatibilityR127
#print axioms QuantumNLS.Ext005CrossJCompatibilityR127.cross_j_D3
#print axioms QuantumNLS.Ext005CrossJCompatibilityR127.EXT005_cross_j_R127
#print axioms QuantumNLS.Ext005CrossJCompatibilityR127.EXT005_single_evolution_R127

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CrossJCompatibilityR127." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CrossJCompatibilityR127." then
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
  Lean.logInfo m!"R127 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
