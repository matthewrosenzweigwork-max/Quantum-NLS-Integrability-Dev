import NlsGge.GK38.AbelianDifferenceOffDiagonalBound
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! UNCOMPILED genuine joint square-mass bridge. Summability is proved
BEFORE changing a product-index tsum to iterated row sums. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p6OmittedMatrix_joint_mass38 (n : ℤ)
    (a : P2Index38 n × P2Index38 n → ℝ) (ha : ∀ p, 0 ≤ a p)
    (e : ℤ → ℝ) (he : Summable (fun m : ℤ => e m^2)) (C : ℝ)
    (hbound : ∀ m r : P2Index38 n,
      a (m,r) ≤ (C^2*e m.val^2)*Lib.c3w m.val r.val^2) :
    Summable a ∧ (∑' p, a p) ≤ C^2*Lib.invSqSum*(∑' m : ℤ, e m^2) := by
  have heSub : Summable (fun m : P2Index38 n => e m.val^2) :=
    he.comp_injective (i := fun m : P2Index38 n => m.val) Subtype.val_injective
  have heMass : (∑' m : P2Index38 n, e m.val^2) ≤ ∑' m : ℤ, e m^2 :=
    Summable.tsum_subtype_le (fun m : ℤ => e m^2) {m : ℤ | m ≠ n}
      (fun _ => sq_nonneg _) he
  have hkernel (m : P2Index38 n) :
      Summable (fun r : P2Index38 n => Lib.c3w m.val r.val^2) ∧
      (∑' r : P2Index38 n, Lib.c3w m.val r.val^2) ≤ Lib.invSqSum := by
    have hw := Lib.summable_c3w_sq m.val
    exact ⟨hw.comp_injective (i := fun r : P2Index38 n => r.val) Subtype.val_injective,
      (Summable.tsum_subtype_le (fun r : ℤ => Lib.c3w m.val r^2)
        {r : ℤ | r ≠ n} (fun _ => sq_nonneg _) hw).trans_eq (Lib.tsum_c3w_sq m.val)⟩
  have hrow (m : P2Index38 n) : Summable (fun r : P2Index38 n => a (m,r)) :=
    ((hkernel m).1.mul_left (C^2*e m.val^2)).of_nonneg_of_le
      (fun r => ha (m,r)) (hbound m)
  have hrowMass (m : P2Index38 n) : (∑' r : P2Index38 n, a (m,r)) ≤
      (C^2*Lib.invSqSum)*e m.val^2 := by
    have hb := (hrow m).tsum_le_tsum (hbound m)
      ((hkernel m).1.mul_left (C^2*e m.val^2))
    rw [tsum_mul_left] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left (hkernel m).2
      (mul_nonneg (sq_nonneg C) (sq_nonneg (e m.val)))).trans_eq (by ring))
  have hdom := heSub.mul_left (C^2*Lib.invSqSum)
  have houter : Summable (fun m : P2Index38 n => ∑' r : P2Index38 n, a (m,r)) :=
    hdom.of_nonneg_of_le (fun m => tsum_nonneg (fun r => ha (m,r))) hrowMass
  have hjoint : Summable a := (summable_prod_of_nonneg (fun p => ha p)).mpr ⟨hrow,houter⟩
  refine ⟨hjoint,?_⟩
  rw [hjoint.tsum_prod]
  have hb := houter.tsum_le_tsum hrowMass hdom
  rw [tsum_mul_left] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left heMass
    (mul_nonneg (sq_nonneg C) Lib.invSqSum_nonneg))

/-- The weighted row used by the ACTUAL difference has genuine square mass. -/
theorem p6WeightedRow_square_summable38 (E d : ℤ → ℝ)
    (hE : Summable (fun m : ℤ => E m^2))
    (hd : Summable (fun m : ℤ => d m^2)) (a : ℝ) (n : ℤ) :
    Summable (fun m : ℤ => (E m*(a+d m)*Lib.c3w m n)^2) := by
  let B : ℝ := ∑' m : ℤ, d m^2
  have hB : 0 ≤ B := tsum_nonneg (fun _ => sq_nonneg _)
  have hdBound (m : ℤ) : d m^2 ≤ B := by
    simpa only [Finset.sum_singleton] using hd.sum_le_tsum ({m} : Finset ℤ)
      (fun _ _ => sq_nonneg _)
  have hdom := hE.mul_left (2*(a^2+B))
  apply hdom.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  have hw0 := Lib.c3w_nonneg m n
  have hw1 := Lib.c3w_le_one m n
  have hw2 : Lib.c3w m n^2 ≤ 1 := by nlinarith
  have hd2 : (a+d m)^2 ≤ 2*(a^2+B) := by nlinarith [sq_nonneg (a-d m),hdBound m]
  calc
    (E m*(a+d m)*Lib.c3w m n)^2 = E m^2*(a+d m)^2*Lib.c3w m n^2 := by ring
    _ ≤ E m^2*(2*(a^2+B))*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd2 (sq_nonneg (E m))) hw2
        (sq_nonneg _) (mul_nonneg (sq_nonneg _) (by positivity))
    _ = (2*(a^2+B))*E m^2 := by ring

theorem p6ActualDifference_offDiagonal_joint_mass38
    (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (hfam : IsolatingFamily38 φ C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (H : ℝ) (hH : 0 ≤ H)
    (hRatio : ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) (n : ℤ) :
    let a : (P2Index38 n × P2Index38 n) → ℝ := fun p =>
      if p.2=p.1 then 0 else
        ‖(p6PaddedJacobian38 n φ s-p6Qstar38 φ s)
          (lp.single 2 p.2.val (1 : ℂ)) p.1.val‖^2
    Summable a ∧
      (∑' p, a p) ≤ (2*c^2*H)^2*Lib.invSqSum*
        (∑' m : ℤ, p2RowEnvelope38 φ s m^2*
          (‖s n‖+p2RowEnvelope38 φ 0 m)^2*Lib.c3w m n^2) := by
  classical
  let T := p6PaddedJacobian38 n φ s-p6Qstar38 φ s
  let E : ℤ → ℝ := p2RowEnvelope38 φ s
  let d : ℤ → ℝ := p2RowEnvelope38 φ 0
  let e : ℤ → ℝ := fun m => E m*(‖s n‖+d m)*Lib.c3w m n
  let a : (P2Index38 n × P2Index38 n) → ℝ := fun p =>
    if p.2=p.1 then 0 else ‖T (lp.single 2 p.2.val (1 : ℂ)) p.1.val‖^2
  obtain ⟨U,hU,_hUW,V,hV,B,_hB,hrow⟩ := p2RowEnvelope_common_l2_bound38 φ hφ s
  have hEs : Summable (fun m : ℤ => E m^2) :=
    (hrow φ (mem_of_mem_nhds hU) s (mem_of_mem_nhds hV)).1
  have hds : Summable (fun m : ℤ => d m^2) := p6CutCenter_envelope_summable38 φ hφ
  have hes : Summable (fun m : ℤ => e m^2) :=
    p6WeightedRow_square_summable38 E d hEs hds ‖s n‖ n
  have ha (p : P2Index38 n × P2Index38 n) : 0 ≤ a p := by
    dsimp [a]
    split_ifs <;> positivity
  have hpoint (m r : P2Index38 n) :
      a (m,r) ≤ ((2*c^2*H)^2*e m.val^2)*Lib.c3w m.val r.val^2 := by
    by_cases hrm : r=m
    · simp only [a,hrm,ite_true]
      positivity
    · have hrmVal : r.val ≠ m.val := fun he => hrm (Subtype.ext he)
      have hh := p6ActualDifference_offDiagonal_bound38 φ hφ C R c N hg hfam s hσ H hH
        hRatio n m.val r.val m.property r.property hrmVal
      have hb : ‖T (lp.single 2 r.val (1 : ℂ)) m.val‖ ≤
          (2*c^2*H)*e m.val*Lib.c3w m.val r.val :=
        hh.trans_eq (by dsimp [e,E,d]; ring)
      simp only [a,hrm,ite_false]
      calc
        _ ≤ ((2*c^2*H)*e m.val*Lib.c3w m.val r.val)^2 :=
          by nlinarith [mul_self_le_mul_self (norm_nonneg _) hb]
        _ = ((2*c^2*H)^2*e m.val^2)*Lib.c3w m.val r.val^2 := by ring
  have hmass := p6OmittedMatrix_joint_mass38 n a ha e hes (2*c^2*H) hpoint
  have heq : (∑' m : ℤ, e m^2) =
      ∑' m : ℤ, p2RowEnvelope38 φ s m^2*(‖s n‖+p2RowEnvelope38 φ 0 m)^2*Lib.c3w m n^2 := by
    apply tsum_congr
    intro m
    dsimp [e,E,d]
    ring
  rw [heq] at hmass
  exact hmass

end
end NlsGge.GK38
