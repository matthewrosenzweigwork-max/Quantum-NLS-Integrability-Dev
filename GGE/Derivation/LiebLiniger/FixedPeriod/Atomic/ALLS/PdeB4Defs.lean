import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Hm1Duhamel
import NlsGge.NLS38.PhysicalFlow38

/-! # Track B (owner-approved contracts, staging step 1): literal predicates, typed Duhamel
definitions and the four H⁻¹ interface lemmas

Copied verbatim from the owner-approved text `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056; revised source sha256
ba827a41f9991fe122194276398b3be414ecc18346f1b3062ebd472a6833b313). The interface lemmas are proved
from the committed generic modules PdeB3Hm1Core/Prop/Duhamel. No theorem command of the 21 main
contracts and no `l2Flow` is contained here. -/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff

/-! ### Literal definitions (owner-approved) -/

def spacetimeMeasure : Measure (ℝ × PhysicalCircle) := (volume : Measure ℝ).prod spatialMeasure

def cubicNL (z : ℂ) : ℂ := 2 * ((‖z‖ ^ 2 : ℝ) : ℂ) * z

structure IsSpacetimeRep (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) : Prop where
  aesm : AEStronglyMeasurable U spacetimeMeasure
  slice : ∀ᵐ t ∂(volume : Measure ℝ), (fun x => U (t, x)) =ᵐ[spatialMeasure] (u t : PhysicalCircle → ℂ)

def IsL4Loc (U : ℝ × PhysicalCircle → ℂ) : Prop :=
  ∀ T : ℝ, MemLp U 4 (spacetimeMeasure.restrict (Set.Icc (-T) T ×ˢ Set.univ))

structure IsSpacetimeTest (φ : ℝ × ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ t x, φ (t, x + 1) = φ (t, x)
  compact_time : ∃ T : ℝ, ∀ t x, T < |t| → φ (t, x) = 0

def stripMeasure : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume.restrict (Set.Ioc 0 1))

def IsDistributionalNLS (U : ℝ × PhysicalCircle → ℂ) : Prop :=
  ∀ φ : ℝ × ℝ → ℂ, IsSpacetimeTest φ →
    let lhs : ℝ × ℝ → ℂ := fun p =>
      U (p.1, (p.2 : PhysicalCircle)) *
        (iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 -
          Complex.I * deriv (fun s => φ (s, p.2)) p.1)
    let rhs : ℝ × ℝ → ℂ := fun p => cubicNL (U (p.1, (p.2 : PhysicalCircle))) * φ p
    Integrable lhs stripMeasure ∧ Integrable rhs stripMeasure ∧
      ∫ p, lhs p ∂stripMeasure = ∫ p, rhs p ∂stripMeasure

def IsL2ClassSolution (u : ℝ → PhysicalL2) : Prop :=
  Continuous u ∧ ∃ U, IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsDistributionalNLS U

/-! ### REVISED H⁻¹ definitions (R1): typed, certified embeddings; no raw sequence decoder -/

/-- `-i e^{i(t-r)∂ₓ²}(2|U(r)|²U(r))` in `H⁻¹`: committed typed maps `freeProp`, `negIMul`, `fnToHm1`
(= `l1ToHm1` on integrable slices, certified by `carrierCoe38_fnToHm1`). -/
def duhamelIntegrand (U : ℝ × PhysicalCircle → ℂ) (t r : ℝ) : SobolevCarrier38 (-1) :=
  freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => cubicNL (U (r, x)))))

/-- The `H⁻¹` Bochner Duhamel identity from time `0`, with interval integrability. -/
def IsHm1Duhamel (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) : Prop :=
  ∀ t : ℝ, IntervalIntegrable (duhamelIntegrand U t) volume 0 t ∧
    l2ToHm1 (u t) = freeProp (-1) t (l2ToHm1 (u 0)) + ∫ r in (0 : ℝ)..t, duhamelIntegrand U t r

def IsL2NLSSolution (u : ℝ → PhysicalL2) : Prop :=
  Continuous u ∧ ∃ U, IsSpacetimeRep u U ∧ IsL4Loc U ∧ IsDistributionalNLS U ∧ IsHm1Duhamel u U

/-! ### The four H⁻¹ interface lemmas (owner-approved statements) -/

theorem cubic_slab_integrable {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) (T : ℝ) :
    Integrable (fun p => cubicNL (U p))
      (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod spatialMeasure) :=
  integrable_cubic_slab (h4 T)

theorem ae_integrable_cubic_slice {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) :
    ∀ᵐ r ∂(volume : Measure ℝ), Integrable (fun x => cubicNL (U (r, x))) spatialMeasure := by
  have h : ∀ k : ℕ, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Icc (-(k : ℝ)) k →
      Integrable (fun x => cubicNL (U (r, x))) spatialMeasure :=
    fun k => ae_integrable_slice (F := fun p => cubicNL (U p)) (cubic_slab_integrable h4 k)
  filter_upwards [ae_all_iff.2 h] with r hr
  obtain ⟨k, hk⟩ := exists_nat_ge |r|
  exact hr k ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩

theorem duhamelIntegrand_intervalIntegrable {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U)
    (t s s' : ℝ) : IntervalIntegrable (duhamelIntegrand U t) volume s s' :=
  intervalIntegrable_duhamel (F := fun p => cubicNL (U p)) (cubic_slab_integrable h4) t s s'

theorem carrierCoe38_duhamelIntegral {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U)
    (t s s' : ℝ) (n : ℤ) :
    carrierCoe38 (-1) (∫ r in s..s', duhamelIntegrand U t r) n =
      ∫ r in s..s', freePhase (t - r) n *
        (-Complex.I * physicalFourier (fun x => cubicNL (U (r, x))) n) :=
  carrierCoe38_duhamel_integral (F := fun p => cubicNL (U p)) (cubic_slab_integrable h4) t s s' n


end LiebLiniger.FixedPeriod.ALLS.PdeB
