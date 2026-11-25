import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G6.G6004
import NlsGge.Atomic.G6.G6015
import NlsGge.Atomic.G6.G6020

/- G6-021 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6021Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6021Aux.
   GK Theorem 20.1 (isospectral set = full torus): MapsTo by landed G6015; InjOn by the G6013 bijectivity / left
   inverse; SurjOn: for z on the physical torus of I(u), |z_n| = |Phi_n(u)| (X-006 Phi_action, landed
   g6_actionSequence_apply); the symmetric truncations s_N = Phi(u) + sum_{|k|<=N} (z - Phi u)_k e_k differ from Phi(u)
   in finitely many coordinates, so Psi(s_N) in isospectralSet u by the G6-018 head; s_N -> z (lp.hasSum_single,
   the finite-coordinate approximation of G6-019 in the physical coordinates), Psi is continuous (G6-014) and the
   isospectral set is closed (landed G6020).  The Cartesian statement is transported through the G6013Sup1 equivalence
   (exists_physicalCartesianEquiv head).  Pending heads (G6018, G6013 conjuncts, G6014 conjunct, G6013Sup1) are
   hypotheses of their exact types, discharged in G6021. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6021Aux
noncomputable section

theorem sum_single_apply (S : Finset ℤ) (f : Lib.L2Z) (n : ℤ) :
    (∑ k ∈ S, lp.single 2 k (f k) : Lib.L2Z) n = if n ∈ S then f n else 0 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a S ha ih
    rw [Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih]
    by_cases h : n = a
    · subst h
      simp [ha]
    · rw [lp.single_apply_ne _ _ _ h]
      simp [h]

theorem tendsto_Icc : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun n => ?_)
  · exact Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab)
  · refine ⟨n.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

/-- Core of G6-021. -/
theorem core21
    (H18 : ∀ (z w : Lib.L2Z) (hrad : ∀ n : ℤ, ‖z n‖^2 = ‖w n‖^2)
      (hfin : {n : ℤ | z n ≠ w n}.Finite),
      (∃ t : ℤ → ℝ, (Function.support t).Finite ∧
        Function.support t ⊆ {n : ℤ | z n ≠ w n} ∧
        ∀ n : ℤ, z n = Complex.exp (-Complex.I * (t n : ℂ)) * w n) ∧
      physicalInverseBirkhoff z ∈ isospectralSet (physicalInverseBirkhoff w))
    (hRbij : Function.Bijective realBirkhoffCartesian)
    (hPL : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hPR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hΨ : AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ)
    (HE : ∃ e : Lib.L2Z ≃L[ℝ] CartesianReal,
      (∀ (z : Lib.L2Z) (n : ℤ),
        e z (true, n) = Real.sqrt 2 * (z n).re ∧
        e z (false, n) = -Real.sqrt 2 * (z n).im) ∧
      ∀ u : PhysicalL2, realBirkhoffCartesian u = e (physicalBirkhoff u))
    (u : PhysicalL2) :
  Set.BijOn realBirkhoffCartesian (isospectralSet u) (actionTorus (actionSequence u)) ∧
  Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)) := by
  have hΨc : Continuous physicalInverseBirkhoff :=
    continuous_iff_continuousAt.2 fun z => (hΨ z (Set.mem_univ _)).continuousAt
  have hsurj : ∀ z : Lib.L2Z, z ∈ physicalActionTorus (actionSequence u) →
      physicalInverseBirkhoff z ∈ isospectralSet u := by
    intro z hz
    have hrad : ∀ n : ℤ, ‖z n‖^2 = ‖physicalBirkhoff u n‖^2 := fun n => by
      rw [hz n, g6_actionSequence_apply, ← sourceFamily.Phi_action u n]
      rfl
    let s : ℕ → Lib.L2Z := fun N => physicalBirkhoff u +
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, lp.single 2 k ((z - physicalBirkhoff u) k)
    have hs_apply : ∀ (N : ℕ) (n : ℤ),
        s N n = if n ∈ Finset.Icc (-(N : ℤ)) N then z n else physicalBirkhoff u n := by
      intro N n
      show (physicalBirkhoff u + ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        lp.single 2 k ((z - physicalBirkhoff u) k) : Lib.L2Z) n = _
      rw [lp.coeFn_add, Pi.add_apply, sum_single_apply]
      by_cases h : n ∈ Finset.Icc (-(N : ℤ)) N
      · rw [if_pos h, if_pos h, lp.coeFn_sub, Pi.sub_apply]
        ring
      · rw [if_neg h, if_neg h, add_zero]
    have hmem : ∀ N : ℕ, physicalInverseBirkhoff (s N) ∈ isospectralSet u := by
      intro N
      have hr : ∀ n : ℤ, ‖s N n‖^2 = ‖physicalBirkhoff u n‖^2 := fun n => by
        rw [hs_apply]
        split_ifs
        · exact hrad n
        · rfl
      have hf : {n : ℤ | s N n ≠ physicalBirkhoff u n}.Finite :=
        (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset (fun n hn => by
          by_contra h'
          exact hn (by rw [hs_apply, if_neg (fun h => h' (Finset.mem_coe.2 h))]))
      have h := (H18 (s N) (physicalBirkhoff u) hr hf).2
      rwa [hPL u] at h
    have htend : Tendsto s atTop (𝓝 z) := by
      have hHS := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)) (by simp)
        (z - physicalBirkhoff u)
      have h2 := (hHS.comp tendsto_Icc).const_add (physicalBirkhoff u)
      have h3 : physicalBirkhoff u + (z - physicalBirkhoff u) = z := by abel
      rw [h3] at h2
      exact h2
    exact (G6020 u).mem_of_tendsto (hΨc.continuousAt.tendsto.comp htend)
      (Eventually.of_forall hmem)
  have hPbij : Set.BijOn physicalBirkhoff (isospectralSet u)
      (physicalActionTorus (actionSequence u)) :=
    ⟨fun v hv => (G6015 u).2 ⟨v, hv, rfl⟩,
      fun a _ b _ hab => hPL.injective hab,
      fun z hz => ⟨physicalInverseBirkhoff z, hsurj z hz, hPR z⟩⟩
  obtain ⟨e, he1, he2⟩ := HE
  refine ⟨⟨fun v hv => (G6015 u).1 ⟨v, hv, rfl⟩, fun a _ b _ hab => hRbij.1 hab, ?_⟩, hPbij⟩
  intro c hc
  have hz : e.symm c ∈ physicalActionTorus (actionSequence u) := by
    intro n
    have h := hc n
    have hce : c = e (e.symm c) := (e.apply_symm_apply c).symm
    rw [hce, (he1 (e.symm c) n).1, (he1 (e.symm c) n).2] at h
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [← h, Complex.sq_norm, Complex.normSq_apply, neg_mul, neg_sq, mul_pow, mul_pow, hs]
    ring
  refine ⟨physicalInverseBirkhoff (e.symm c), hsurj _ hz, ?_⟩
  rw [he2, hPR, e.apply_symm_apply]

end
end G6021Aux
end NlsGge.GKDefinitionDesign
