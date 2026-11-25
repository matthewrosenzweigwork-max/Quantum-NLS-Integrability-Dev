import NlsGge.GK38.AbelianDenominator
import Mathlib.Order.Filter.Finite

/-! One actual input neighborhood preserves ALL strict sigma placements in the SAME
supplied original family. UNCOMPILED source preparation; no family replacement. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p3Input_all_own_disc38 (s₀ : Lib.L2Seq)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N)
    (hbase : ∀ n : ℤ, Lib.sigmaOf s₀ n ∈ ball (C n) (R n)) :
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧
      ∀ s ∈ V, ∀ n : ℤ, Lib.sigmaOf s n ∈ ball (C n) (R n) := by
  classical
  obtain ⟨Vt,hVt,Nt,ht⟩ := p2Input_tail_own_disc38 s₀ C R c N hgeom
  let S : Finset ℤ := Finset.Icc (-(Nt : ℤ)) (Nt : ℤ)
  let A : ℤ → Set Lib.L2Seq := fun n => {s | Lib.sigmaOf s n ∈ ball (C n) (R n)}
  have hA (n : ℤ) : A n ∈ 𝓝 s₀ := by
    have heval : Continuous (fun s : Lib.L2Seq => s n) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous
    have hcoord : Continuous (fun s : Lib.L2Seq => Lib.sigmaOf s n) := by
      exact continuous_const.add heval
    exact (isOpen_ball.preimage hcoord).mem_nhds (hbase n)
  refine ⟨Vt ∩ ⋂ n ∈ S, A n,
    inter_mem hVt ((Filter.biInter_finset_mem S).mpr (fun n _ => hA n)),?_⟩
  intro s hs n
  by_cases hn : n ∈ S
  · exact mem_iInter.mp (mem_iInter.mp hs.2 n) hn
  · have hnt : (Nt : ℤ) < |n| := by
      apply lt_of_not_ge
      intro hle
      exact hn (Finset.mem_Icc.mpr (abs_le.mp hle))
    exact ht s hs.1 n hnt

end
end NlsGge.GK38
