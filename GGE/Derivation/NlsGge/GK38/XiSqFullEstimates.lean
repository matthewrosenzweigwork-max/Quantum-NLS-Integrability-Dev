import NlsGge.GK38.XiSqNormalizedTail

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Actual candidate errors have a full-index local square bound, including every finite head. -/
theorem a5XiSqError_l2_38 (g : ℤ → PotPair → ℂ) (hspec : ∀ n, XiSqSpec38 n (g n))
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => g n φ-1) φ₀ := by
  classical
  obtain ⟨Ut,hUt,_hUtW,N,B,hB,ht⟩ := a5XiSqError_tail_l2_majorant38 g hspec φ₀ hφ₀
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  obtain ⟨Uf,hUf,F,hF,hf⟩ := finite_continuous_seq_bound38
    (fun φ n => g n φ-1) S φ₀
    (fun n _ => ((hspec n).1 φ₀ hφ₀).continuousAt.sub continuousAt_const)
  refine ⟨Ut ∩ Uf,inter_mem hUt hUf,(S.card:ℝ)*F^2+2*B,?_⟩
  intro φ hφ
  obtain ⟨b,hb0,hbs,hbB,hb⟩ := ht φ hφ.1
  have htail (n : ℤ) (hn : n ∉ S) : ‖g n φ-1‖ ≤ b n+0*(0:ℝ) := by
    have hnf : (N:ℤ) < |n| := by
      have hnot : ¬ (-(N:ℤ) ≤ n ∧ n ≤ (N:ℤ)) := by simpa only [S,Finset.mem_Icc] using hn
      by_contra h
      exact hnot (abs_le.mp (not_lt.mp h))
    simpa only [zero_mul,mul_zero,add_zero] using hb n hnf
  have hz : Summable (fun _ : ℤ => (0:ℝ)^2) := by simp
  have h := finite_tail_square_sum38 (fun n => g n φ-1) S F 0 B 0 hF le_rfl
    b (fun _ => 0) hb0 (fun _ => le_rfl) hbs hz hbB (by simp) (hf φ hφ.2) htail
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,mul_zero,add_zero] using h

/-- The full common-neighbourhood slit-plane and near-one target, for every actual candidate. -/
theorem xiSqNearOne38_proved : XiSqNearOne38 := by
  intro g hspec φ₀ hφ₀
  exact a5XiSq_near_one_of_l2_38 g hspec (a5XiSqError_l2_38 g hspec) φ₀ hφ₀

/-- Full local square summability of the principal square-root errors, including the finite head. -/
theorem xiSqrtL2NearOne38_proved : XiSqrtL2NearOne38 := by
  intro g hspec φ₀ hφ₀
  exact a5XiSqrt_l2_of_l2_38 g φ₀ (a5XiSqError_l2_38 g hspec φ₀ hφ₀)

end
end NlsGge.GK38
