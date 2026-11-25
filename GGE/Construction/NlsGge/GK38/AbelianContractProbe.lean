import NlsGge.GK38.AbelianRealImage

/-! Exact prospective P2 target witnesses. These package previously earned proofs;
no extra mathematical credit is claimed for the packaging declarations. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.P2ContractProbe
noncomputable section

theorem extension (n : ℤ) (s : P2Space38 n) :
    (p2Extend38 n s) n=0 ∧ (∀ m : P2Index38 n, (p2Extend38 n s) m.1=s m) ∧
      ‖p2Extend38 n s‖=‖s‖ :=
  ⟨p2Extend_self38 n s,p2Extend_at38 n s,p2Extend_norm38 n s⟩

theorem numerator (n : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) univ :=
  p2FullNumerator_joint_analytic38 n

theorem integrability (m n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) :
    CircleIntegrable (fun z => p2FullNumerator38 n s z/canonRoot38 φ z)
      (discC φ m) (discR φ m) := p2Period_integrable38 m n φ hφ s

theorem family (φ : PotPair) (hφ : φ ∈ gkW) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (m : ℤ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    circleIntegral (fun z => f z/canonRoot38 φ z) (C0 m) (R0 m)=
      circleIntegral (fun z => f z/canonRoot38 φ z) (C1 m) (R1 m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ C0 C1 R0 R1 h0 h1 m f hf).2.2

theorem coordinate (n m : ℤ) :
    AnalyticOnNhd ℂ (fun p : PotPair × Lib.L2Seq => (((n-m:ℤ):ℂ))*
      abelianPeriod38 m p.1 (p2FullNumerator38 n p.2))
      (gkW ×ˢ (univ : Set Lib.L2Seq)) := p2FullCoordinate_analytic38 n m

theorem uniform (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ n : ℤ,
        Summable (fun m : P2Index38 n => ‖(((n-m.1:ℤ):ℂ))*
          abelianPeriod38 m.1 φ (p2FullNumerator38 n s)‖^2) ∧
        (∑' m : P2Index38 n, ‖(((n-m.1:ℤ):ℂ))*
          abelianPeriod38 m.1 φ (p2FullNumerator38 n s)‖^2) ≤ B :=
  p2OmittedPeriod_uniform_l2_bound38 φ₀ hφ₀ s₀

theorem realization (n : ℤ) : ∃ F : (PotPair × P2Space38 n) → P2Space38 n,
    (∀ p : PotPair × P2Space38 n, p.1 ∈ gkW →
      ∀ m : P2Index38 n, F p m=p2FnCoord38 n p m) ∧
    AnalyticOnNhd ℂ F (gkW ×ˢ (univ : Set (P2Space38 n))) ∧
    (∀ (u : PhysicalL2) (s : P2Space38 n), p2RealSeq38 n s →
      ∀ m : P2Index38 n, (F (realSlice u,s) m).im=0) :=
  ⟨p2Fn38 n,p2Fn_apply38 n,p2Fn_analytic38 n,p2Fn_real38 n⟩

theorem zero_gap (m n : ℤ) (hmn : m ≠ n) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (U : Set ℂ) (f : ℂ → ℂ) (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hUs : sphere (C m) (R m) ⊆ U) (hf : AnalyticOnNhd ℂ f U)
    (hfReal : ∀ x : ℝ, (x:ℂ) ∈ segment ℝ (lamMinus (realSlice u) m)
      (lamPlus (realSlice u) m) → (f (x:ℂ)).im=0)
    (hz : circleIntegral (fun z => f z/canonRoot38 (realSlice u) z) (C m) (R m)=0) :
    ∃ x : ℝ, (x:ℂ) ∈ segment ℝ (lamMinus (realSlice u) m)
      (lamPlus (realSlice u) m) ∧ f (x:ℂ)=0 :=
  p2Abelian_zero_in_gap38 m n hmn u C R hfam U f hUo hUc hUs hf hfReal hz

theorem complex_norm (a b c : ℂ) (r B : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ ball c r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hB : 0 ≤ B)
    (hfB : ∀ z ∈ segment ℝ a b, ‖f z‖ ≤ B) :
    CircleIntegrable (fun z => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r ∧
    ‖circleIntegral (fun z => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r‖ ≤ 2*Real.pi*B :=
  p2StdRoot_integral_norm_bound38 a b c r B hr hcut f hf hB hfB

theorem real_mean (a b : ℝ) (hab : a ≤ b) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ (a:ℂ) (b:ℂ) ⊆ ball c r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hreal : ∀ x ∈ Icc a b, (f (x:ℂ)).im=0) :
    ∃ x ∈ Icc a b, (1/(2*(Real.pi:ℂ)*Complex.I))*
      circleIntegral (fun z => f z/stdRoot38 (((a:ℂ)+b)/2) (((b:ℂ)-a)^2) z) c r = -f (x:ℂ) :=
  p2StdRoot_real_mean_value38 a b hab c r hr hcut f hf hreal

#print axioms extension
#print axioms numerator
#print axioms integrability
#print axioms family
#print axioms coordinate
#print axioms uniform
#print axioms realization
#print axioms zero_gap
#print axioms complex_norm
#print axioms real_mean
end
end NlsGge.GK38.P2ContractProbe
