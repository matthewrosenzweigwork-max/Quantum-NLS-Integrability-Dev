import Mathlib
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST035
import NlsGge.Atomic.KST.KST038
import NlsGge.Atomic.KST.KST041
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host

/- KST-042 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST042.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-042"
   (identical in gpt6pro_followup1..10; no Pro round 5-12 entry touches KST-042).  No repair of the head.
   Route (source Proposition 6.1; packet skeleton): (1) KST-041 for the weight omega = w*v gives a preimage
   z in the closed omega-ball of M with F_omega z = y; (2) KST-035 identifies the coefficients of F_omega z with
   adaptedCoefficients N (weightedPotential omega z), so those equal the coefficients of the w-ball point x;
   (3) the restriction of z to Weighted w (v >= 1) lies in the w-ball of M, has the same physical potential
   (KST033Support.wp_restriction), so F_w (restriction z) = F_w x by the definition of adaptedFourier;
   (4) F_w is injective on the w-ball (KST-038 for the secondary weight 1, transported along
   productWeight w 1 = w), hence restriction z = x and the potentials agree. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

namespace KST042W

theorem restriction_mem_componentBall (ω ν : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    [Fact (∀ m : ℤ, 0 < periodOneWeight ν m ^ 2)]
    (hων : ∀ k, ν k ^ 2 ≤ ω k ^ 2) (R : ℝ) (x : Weighted ω)
    (hx : x ∈ componentBall ω R) :
    weightedRestriction ω ν hων x ∈ componentBall ν R := by
  intro ch
  have h := weightedComparison_norm_le (fun m => periodOneWeight ω m ^ 2)
    (fun m => periodOneWeight ν m ^ 2) 1 (by norm_num)
    (fun m => by simpa [periodOneWeight] using hων (2*m)) (x ch)
  have e : (weightedRestriction ω ν hων x) ch =
      weightedComparison (fun m => periodOneWeight ω m ^ 2)
        (fun m => periodOneWeight ν m ^ 2) 1 (by norm_num)
        (fun m => by simpa [periodOneWeight] using hων (2*m)) (x ch) := rfl
  rw [e]
  rw [Real.sqrt_one, one_mul] at h
  exact h.trans (hx ch)

theorem injOn_transport (w u : ℤ → ℝ) (M : ℝ) (N : ℕ) (h : u = w) :
    (∀ hu : (∀ k, 1 ≤ u k), letI := weightFact u hu;
      Set.InjOn (adaptedFourier u hu N) (componentBall u M)) →
    (∀ hw1 : (∀ k, 1 ≤ w k), letI := weightFact w hw1;
      Set.InjOn (adaptedFourier w hw1 N) (componentBall w M)) := by
  subst h
  exact id

end KST042W

theorem kst042 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact w hw.one_le
  letI := weightFact ω hω
  ∀ x ∈ componentBall w M, ∀ y ∈ componentBall ω (M/2),
    weightedCoeffs ω y =
      adaptedCoefficients (adaptedThreshold w M) (weightedPotential w hw.one_le x) →
    ∃ z ∈ componentBall ω M,
      weightedPotential ω hω z = weightedPotential w hw.one_le x ∧
      adaptedFourier ω hω (adaptedThreshold w M) z = y := by
  intro ω hω
  letI := weightFact w hw.one_le
  letI := weightFact ω hω
  intro x hx y hy hcoef
  have hM0 : 0 < M := by linarith
  have hv1 : ∀ k, 1 ≤ v k := hv.1.1
  -- (1) a preimage of y in the closed omega-ball (KST-041)
  have h41 := kst041 w Cw M hM hw hunbounded v hv
  obtain ⟨-, himg, -⟩ := h41
  obtain ⟨z, hz, hFz⟩ := himg hy
  -- (2) coefficients of F z
  have hz2 : z ∈ componentBall ω (2*M) := fun ch => (hz ch).trans (by linarith)
  have hcz : weightedCoeffs ω (adaptedFourier ω hω (adaptedThreshold w M) z) =
      adaptedCoefficients (adaptedThreshold w M) (weightedPotential ω hω z) :=
    ((kst035 w Cw M hM hw hunbounded).2.2 v hv z hz2).1
  rw [hFz, hcoef] at hcz
  -- (3) restriction to the w-space
  have hων : ∀ k, w k ^ 2 ≤ ω k ^ 2 := by
    intro k
    have h1 := hw.one_le k
    have h2 := hv1 k
    have h3 : w k ≤ ω k := by
      show w k ≤ w k * v k
      nlinarith
    exact pow_le_pow_left₀ (by linarith) h3 2
  have hwp : weightedPotential w hw.one_le (weightedRestriction ω w hων z) =
      weightedPotential ω hω z :=
    KST033S.wp_restriction ω w hω hw.one_le hων z
  have hz'mem : weightedRestriction ω w hων z ∈ componentBall w M :=
    KST042W.restriction_mem_componentBall ω w hων M z hz
  have hFeq : adaptedFourier w hw.one_le (adaptedThreshold w M) (weightedRestriction ω w hων z) =
      adaptedFourier w hw.one_le (adaptedThreshold w M) x := by
    unfold adaptedFourier
    rw [hwp, ← hcz]
  -- (4) injectivity of F_w on the w-ball (KST-038 for the secondary weight 1)
  have hv1sec : SecondaryWeight (fun _ : ℤ => (1 : ℝ)) :=
    ⟨⟨fun _ => le_rfl, fun _ => rfl, fun _ _ _ => le_rfl⟩,
      fun k l => by simp⟩
  have hinjProd := (kst038 w Cw M hM hw hunbounded (fun _ : ℤ => (1 : ℝ)) hv1sec).2.1
  have hprod : productWeight w (fun _ : ℤ => (1 : ℝ)) = w := by
    funext k; simp [productWeight]
  have hinjw : Set.InjOn (adaptedFourier w hw.one_le (adaptedThreshold w M)) (componentBall w M) :=
    KST042W.injOn_transport w (productWeight w (fun _ : ℤ => (1 : ℝ))) M (adaptedThreshold w M)
      hprod (fun hu => hinjProd) hw.one_le
  have hzx : weightedRestriction ω w hων z = x := hinjw hz'mem hx hFeq
  refine ⟨z, hz, ?_, hFz⟩
  rw [← hwp, hzx]

end NlsGge.ThirdConsultation.KST
end
