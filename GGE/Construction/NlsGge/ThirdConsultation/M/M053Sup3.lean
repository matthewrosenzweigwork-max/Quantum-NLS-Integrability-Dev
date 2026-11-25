import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairPotentialProbe
import NlsGge.GK38.PairVolterraProbe
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI
import NlsGge.Atomic.M.M003
import NlsGge.Atomic.G1.G1036
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.M.M053Sup2

                                                        
                                                                                                          
                                                                                                               
                                                                                                    
                                                      
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.HierarchyRiccati.Core
attribute [local instance] Classical.propDecidable

local instance spatialFiniteM053 : IsFiniteMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

theorem productInL2_comm' (u v : PhysicalL2) (h : productInL2 u v) : productInL2 v u := by
  have e : (fun x : PhysicalCircle => v x * u x) = fun x : PhysicalCircle => u x * v x :=
    funext fun x => mul_comm _ _
  unfold productInL2 at h ⊢
  rw [e]; exact h

theorem physicalFourier_constL2 (c : ℂ) (n : ℤ) :
    physicalFourier (⇑(constL2 c)) n = if n = 0 then c else 0 := by
  unfold physicalFourier
  have h : fourierCoeff (⇑(constL2 c)) n = fourierCoeff (fun _ : PhysicalCircle => c) n := by
    exact congrFun (fourierCoeff_congr_ae (Lp.coeFn_const 2 spatialMeasure c)) n
  rw [h]
  have h2 : (fun _ : PhysicalCircle => c) = fun x : PhysicalCircle => c * fourier 0 x := by
    funext x; simp
  rw [h2, fourierCoeff.const_mul]
  have h3 := congrFun (fourierCoeff_fourier (T := 1) (0 : ℤ)) n
  rw [h3]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [hn]

theorem physicalSobolev_constL2 (c : ℂ) : physicalSobolev 1 (constL2 c) := by
  rw [physicalSobolev_iff_ordinary, NlsGge.Atomic.LIB006.sobolev_one_iff']
  refine summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)
  have : n ≠ 0 := by simpa using hn
  rw [physicalFourier_constL2]
  simp [this]

theorem weakDerivative_constL2 (c : ℂ) : weakDerivative (constL2 c) = 0 := by
  apply physicalFourierL2.injective
  apply Subtype.ext
  funext n
  have h2 := physicalFourier_weakDerivative (constL2 c) (physicalSobolev_constL2 c) n
  change physicalFourierL2 (weakDerivative (constL2 c)) n = physicalFourierL2 0 n
  rw [physicalFourierL2_apply, h2, map_zero]
  rw [physicalFourier_constL2]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [hn]

theorem weakDerivative_add_H1 (u v : PhysicalL2) (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    physicalSobolev 1 (u + v) ∧ weakDerivative (u + v) = weakDerivative u + weakDerivative v := by
  have hs : physicalSobolev 1 (u + v) := by
    have := (psn_add 1 (by simpa using hu) (by simpa using hv)).1
    simpa using this
  refine ⟨hs, weakDerivative_eq_of_hasWeak _ _ hs ?_⟩
  refine (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mpr ?_
  intro n
  change physicalFourier ((weakDerivative u + weakDerivative v : PhysicalL2) : PhysicalCircle → ℂ) n =
    NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier ((u + v : PhysicalL2) : PhysicalCircle → ℂ) n
  rw [NlsGge.Atomic.LIB006.physicalFourier_add, NlsGge.Atomic.LIB006.physicalFourier_add,
    physicalFourier_weakDerivative u hu, physicalFourier_weakDerivative v hv]
  simp [NlsGge.Atomic.LIB002.fourierMultiplier]
  ring

/-- Realisation invariant for a polynomial `P` over the jet family `J`. -/
def PolyRealised (J : Jet → PhysicalL2) (P : Poly) : Prop :=
  ∃ w : PhysicalL2, physicalSobolev 1 w ∧
    (∀ᵐ x : ℝ, coverRep38 w x = polynomialEvaluation (fun v => coverRep38 (J v) x) P) ∧
    (∀ᵐ x : ℝ, coverRep38 (weakDerivative w) x =
      polynomialEvaluation (fun v => coverRep38 (J v) x) (spatialD P))

theorem polyRealised_of_jetOrd (J : Jet → PhysicalL2) (r : ℕ)
    (hJ1 : ∀ v : Jet, v.2 ≤ r → physicalSobolev 1 (J v))
    (hJd : ∀ v : Jet, v.2 ≤ r → weakDerivative (J v) = J (v.1, v.2 + 1))
    (P : Poly) (hP : NlsGge.Atomic.M003.jetOrd r P) : PolyRealised J P := by
  have hmem := NlsGge.Atomic.M003.mem_jetAlg_of_jetOrd hP
  unfold NlsGge.Atomic.M003.jetAlg at hmem
  clear hP
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨J v, hJ1 v hv, Filter.Eventually.of_forall (fun x => by simp), ?_⟩
    rw [hJd v hv]
    exact Filter.Eventually.of_forall (fun x => by simp)
  | algebraMap c =>
    refine ⟨constL2 (c : ℂ), physicalSobolev_constL2 _, ?_, ?_⟩
    · filter_upwards [coverRep38_const_ae (c : ℂ)] with x hx
      rw [hx, MvPolynomial.algebraMap_eq]
      simp
    · rw [weakDerivative_constL2]
      filter_upwards [coverRep38_zero_ae] with x hx
      rw [hx, Derivation.map_algebraMap]
      simp
  | add x y _ _ hx hy =>
    obtain ⟨w1, h1, e1, d1⟩ := hx
    obtain ⟨w2, h2, e2, d2⟩ := hy
    obtain ⟨hs, hd⟩ := weakDerivative_add_H1 w1 w2 h1 h2
    refine ⟨w1 + w2, hs, ?_, ?_⟩
    · filter_upwards [coverRep38_add_ae w1 w2, e1, e2] with t a b c
      rw [a, b, c]; simp
    · rw [hd]
      filter_upwards [coverRep38_add_ae (weakDerivative w1) (weakDerivative w2), d1, d2] with t a b c
      rw [a, b, c]; simp
  | mul x y _ _ hx hy =>
    obtain ⟨w1, h1, e1, d1⟩ := hx
    obtain ⟨w2, h2, e2, d2⟩ := hy
    obtain ⟨hpd, hps, hpw⟩ := weakDerivative_physicalProduct w1 w2 h1 h2
    refine ⟨physicalProduct w1 w2, hps, ?_, ?_⟩
    · filter_upwards [g36_s2b_coverRep_mul_ae w1 w2 hpd, e1, e2] with t a b c
      rw [a, b, c]; simp
    · rw [hpw]
      have p1 : productInL2 (weakDerivative w1) w2 :=
        productInL2_comm' _ _ (productInL2_of_H1 w2 (weakDerivative w1) h2)
      have p2 : productInL2 w1 (weakDerivative w2) := productInL2_of_H1 w1 _ h1
      filter_upwards [coverRep38_add_ae (physicalProduct (weakDerivative w1) w2)
          (physicalProduct w1 (weakDerivative w2)),
        g36_s2b_coverRep_mul_ae _ _ p1, g36_s2b_coverRep_mul_ae _ _ p2, e1, e2, d1, d2]
        with t a b c e1' e2' d1' d2'
      rw [a, b, c, e1', e2', d1', d2', Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      ring

end
end NlsGge.ThirdConsultation.M
