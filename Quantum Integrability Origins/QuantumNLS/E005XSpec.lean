import QuantumNLS.Ext005CrossJCompatibilityR127
/-! integrator-authored trusted spec for EXT-005 cross-j lift (review record r68 PASS): headline statement(s) copied verbatim from Ext005CrossJCompatibilityR127 (QuantumNLS.Ext005CrossJCompatibilityR127). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open Set Filter ContinuousLinearMap MeasureTheory
namespace QuantumNLS.E005XSpec
open QuantumNLS.Ext005CrossJCompatibilityR127
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

set_option maxHeartbeats 8000000 in
theorem EXT005_cross_j_R127_spec (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≤ k)
    (l r : ℝ) (hlr : l ≤ r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) k) :
    ∀ t ∈ Icc l r,
      fixedCurve B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x (domain_mono hjk hx) t =
      fixedCurve B M A hM hA hB hs u₀ k hk l r hlr s hs₀ x hx t := by
  exact QuantumNLS.Ext005CrossJCompatibilityR127.EXT005_cross_j_R127 B M A hM hA hB hs u₀ j k hj hk hjk l r hlr s hs₀ x hx

set_option maxHeartbeats 8000000 in
theorem EXT005_single_evolution_R127_spec :
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
  exact QuantumNLS.Ext005CrossJCompatibilityR127.EXT005_single_evolution_R127 B M A hM hA hB hs u₀

end QuantumNLS.E005XSpec
#print axioms QuantumNLS.E005XSpec.EXT005_cross_j_R127_spec
#print axioms QuantumNLS.E005XSpec.EXT005_single_evolution_R127_spec
