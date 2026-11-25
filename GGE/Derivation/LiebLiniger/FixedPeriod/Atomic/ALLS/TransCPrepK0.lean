import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB12Agree
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB14Cont
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransAFinalA
import NlsGge.Atomic.PDE.PDE066

/-! # Trunk C PREPARATORY lemmas, package K0 (NOT approved, NOT admitted, NOT rooted)

Author: Claude Opus 5.5 (preparatory author P2, trunk C).  Not self-reviewed, not accepted.
Namespace `NlsGge.ALLS.TransCPrep`; every declaration carries the non-approved prefix `prep_`.
Imports the genuine admitted Track B modules (`PdeB12Agree`, `PdeB14Cont`, hence `PdeB10Flow`, `PdeB11Group`, `PdeB13Local`),
Track A `TransAFinalA` and `PDE066`; no stub.

TYPE COINCIDENCE NOTE: `prep_action_invariant` has exactly the type of the pending (NOT yet
owner-approved) trunk C command C-ACTION `allS_action_invariant` in `STATEMENTS_TRUNK_C.md`
(same binders `u t n`, same conclusion).  This is intended so that approval can later re-label it.

Binders and conclusions (one line each):
* `prep_continuous_coord (n)`: for every mode `n : ℤ`, the coordinate map `ℓ²(ℤ) → ℂ`, `z ↦ z n`, is continuous.
* `prep_l2Flow_finite_rotation (u) (hfin) (t) (n)`: for every `u ∈ L²(ℝ/ℤ)` whose Birkhoff
  coordinates `Φ u` have finite support, every time `t` and every mode `n` (zero coordinates included),
  `Φ_n(l2Flow t u) = exp(-i t actualOmega n (I(Φ u))) Φ_n(u)` with `I(z)_k = ‖z_k‖²` (`actions`).
* `prep_norm_l2Flow_finite (u) (hfin) (t) (n)`: under the same finite-support premise,
  `‖Φ_n(l2Flow t u)‖ = ‖Φ_n(u)‖`.
* `prep_action_invariant (u) (t) (n)`: for EVERY `u ∈ L²`, every real `t`, every mode `n`,
  `‖Φ_n(l2Flow t u)‖ = ‖Φ_n(u)‖` (no hypotheses).
Here `Φ = physicalBirkhoff`, `Ψ = physicalInverseBirkhoff` and `l2Flow` is Track B's genuine flow.

Route (PROOF_PLAN_TRUNK_C.md, C-ACTION): finite Birkhoff support ⇒ `H¹` (G6029) ⇒
`l2Flow = nlsFlowL2` (`l2Flow_eq_nlsFlowL2`) ⇒ `actual_finitegap_rotation`.  All data: the finite
partial sums `q S = Σ_{i∈S} single i (Φ u)_i` converge to `Φ u` in `ℓ²` (`lp.hasSum_single`),
`Ψ (q S) → Ψ (Φ u) = u` (continuity of the analytic `Ψ`), `Φ (Ψ (q S)) = q S` has finite support,
then continuity of `l2Flow t`, `Φ` and the coordinate passes the identity to the limit.  The limit is
taken along the `atTop` filter on `Finset ℤ` (no sequence extraction).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common
open NlsGge.SpectralFoundations NlsGge.NLS38
open LiebLiniger.FixedPeriod.ALLS.PdeB NlsGge.ALLS.TransA

namespace NlsGge.ALLS.TransCPrep

/-- Coordinate evaluation on `ℓ²(ℤ)` is continuous (1-Lipschitz). -/
theorem prep_continuous_coord (n : ℤ) : Continuous fun z : Lib.L2Z => (z : ℤ → ℂ) n := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (x - y) n
  simpa [lp.coeFn_sub] using h

/-- Finite Birkhoff support: the genuine `l2Flow` rotates every coordinate with rate `actualOmega`. -/
theorem prep_l2Flow_finite_rotation (u : PhysicalL2)
    (hfin : FiniteSupportSequence (physicalBirkhoff u)) (t : ℝ) (n : ℤ) :
    (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
      Complex.exp (-Complex.I *
        ((t * actualOmega n (actions (physicalBirkhoff u)) : ℝ) : ℂ)) *
        (physicalBirkhoff u : ℤ → ℂ) n := by
  have hgap : NlsGge.ThirdConsultation.finiteGap u := (G6029 u).1.1 hfin
  have hu : SobolevSquareSummable 1 (physicalFourier u) := by
    have h := (fourierSeq38_mem_iff _ u).1 ((G6029 u).2.1 hgap 1)
    rwa [Nat.cast_one] at h
  rw [l2Flow_eq_nlsFlowL2 u hu t]
  exact actual_finitegap_rotation u hfin t n

/-- Finite Birkhoff support: the genuine `l2Flow` preserves every coordinate modulus. -/
theorem prep_norm_l2Flow_finite (u : PhysicalL2)
    (hfin : FiniteSupportSequence (physicalBirkhoff u)) (t : ℝ) (n : ℤ) :
    ‖(physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n‖ = ‖(physicalBirkhoff u : ℤ → ℂ) n‖ := by
  rw [prep_l2Flow_finite_rotation u hfin t n, norm_mul, Complex.norm_exp]
  have hre : (-Complex.I *
      ((t * actualOmega n (actions (physicalBirkhoff u)) : ℝ) : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, one_mul]

/-- All-data action preservation (type coincides with the pending C-ACTION command). -/
theorem prep_action_invariant (u : PhysicalL2) (t : ℝ) (n : ℤ) :
    ‖(physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n‖ = ‖(physicalBirkhoff u : ℤ → ℂ) n‖ := by
  obtain ⟨hL, hR, hA, hAinv, -⟩ := actual_birkhoff_bindings
  have hΦ : Continuous physicalBirkhoff := continuousOn_univ.mp hA.continuousOn
  have hΨ : Continuous physicalInverseBirkhoff := continuousOn_univ.mp hAinv.continuousOn
  let q : Finset ℤ → Lib.L2Z := fun S =>
    ∑ i ∈ S, lp.single (E := fun _ : ℤ => ℂ) (2 : ENNReal) i ((physicalBirkhoff u : ℤ → ℂ) i)
  have hpartial : Tendsto q atTop (𝓝 (physicalBirkhoff u)) :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top
      (physicalBirkhoff u)
  have hcoord (S : Finset ℤ) (k : ℤ) :
      (q S : ℤ → ℂ) k = if k ∈ S then (physicalBirkhoff u : ℤ → ℂ) k else 0 := by
    simp only [q, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  have hfin (S : Finset ℤ) :
      FiniteSupportSequence (physicalBirkhoff (physicalInverseBirkhoff (q S))) := by
    rw [hR (q S)]
    refine S.finite_toSet.subset fun k hk => ?_
    by_contra hkS
    have hkS' : k ∉ S := by simpa using hkS
    exact hk (by rw [hcoord]; simp [hkS'])
  have hu : Tendsto (fun S => physicalInverseBirkhoff (q S)) atTop (𝓝 u) := by
    have h := (hΨ.tendsto _).comp hpartial
    rwa [hL u] at h
  have hflow : Tendsto (fun S => l2Flow t (physicalInverseBirkhoff (q S))) atTop
      (𝓝 (l2Flow t u)) :=
    ((continuous_l2Flow.comp (continuous_const.prodMk continuous_id)).tendsto u).comp hu
  have hlhs : Tendsto
      (fun S => ‖(physicalBirkhoff (l2Flow t (physicalInverseBirkhoff (q S))) : ℤ → ℂ) n‖)
      atTop (𝓝 ‖(physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n‖) :=
    (((continuous_norm.comp (prep_continuous_coord n)).comp hΦ).tendsto _).comp hflow
  have hrhs : Tendsto (fun S => ‖(q S : ℤ → ℂ) n‖) atTop
      (𝓝 ‖(physicalBirkhoff u : ℤ → ℂ) n‖) :=
    ((continuous_norm.comp (prep_continuous_coord n)).tendsto _).comp hpartial
  have heq : (fun S => ‖(physicalBirkhoff (l2Flow t (physicalInverseBirkhoff (q S))) : ℤ → ℂ) n‖) =
      fun S => ‖(q S : ℤ → ℂ) n‖ := by
    funext S
    rw [prep_norm_l2Flow_finite _ (hfin S) t n, hR (q S)]
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

end NlsGge.ALLS.TransCPrep
