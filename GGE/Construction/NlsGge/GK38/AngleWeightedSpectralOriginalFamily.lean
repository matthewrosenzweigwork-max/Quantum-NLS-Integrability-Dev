import NlsGge.GK38.AngleRatioSpectralDerivativeAllCuts
import NlsGge.GK38.AngleRegularFactorSpectralDerivative
import NlsGge.GK38.IsolatingPersistence

/-! Fixed ORIGINAL-family form of the actual weighted spectral derivative
majorant. This lets a genuine compact input cover use ONE supplied family
and its earned persistence, before ANY seed-dependent local bound. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleRegularFactor_weighted_spectral_derivative_l2_original_family38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfamily : IsolatingFamily38 φ₀ C R)
    (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ nhds s₀ ∧
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ φ ∈ U, IsolatingFamily38 φ C R ∧
        ∀ s ∈ V, ∀ n : ℤ,
          Lib.sigmaOf s n ∈ closedBall (C n) (R n) →
          ∃ b : ℤ → ℝ, (∀ m, 0 ≤ b m) ∧
            Summable (fun m : ℤ => b m^2) ∧ (∑' m : ℤ, b m^2) ≤ B ∧
            ∀ m : ℤ, n ≠ m →
              ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
                DifferentiableAt ℂ
                  (fun w => angleRegularFactor38 n m ((φ,s),w)) z ∧
                ‖(((n-m : ℤ) : ℂ))*
                  deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤ b m := by
  obtain ⟨Ud,hUd,hUdW,Vd,hVd,Bd,hBd,hd⟩ :=
    angleOmittedRatio_spectral_deriv_all_cut_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨Uh,hUh,_hUhW,Vh,hVh,H,hH,hh⟩ :=
    p2OmittedRatio_all_cut_bound38 φ₀ hφ₀ s₀
  obtain ⟨ρ,hρ,c,Ng,hgeom,hspec⟩ := fixed_family_persistence38 φ₀ C R hfamily
  let Ug : Set PotPair := ball φ₀ ρ
  have hUg : Ug ∈ nhds φ₀ := ball_mem_nhds φ₀ hρ
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hgeom.2.2.1
  let A : ℝ := c^2*H
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) hH
  refine ⟨Ud ∩ (Uh ∩ Ug),inter_mem hUd (inter_mem hUh hUg),
    fun φ hφ => hUdW hφ.1,Vd ∩ Vh,inter_mem hVd hVh,
    2*c^2*Bd+2*A^2*Lib.invSqSum,by positivity [Lib.invSqSum_nonneg],?_⟩
  intro φ hφ
  have hfam : IsolatingFamily38 φ C R := ⟨c,Ng,hgeom,hspec φ hφ.2.2⟩
  refine ⟨hfam,?_⟩
  intro s hs n hσ
  obtain ⟨d,hd0,hds,hdB,hdpoint⟩ := hd φ hφ.1 s hs.1
  let b : ℤ → ℝ := fun m => c*d m+A*Lib.c3w n m
  have hb0 (m : ℤ) : 0 ≤ b m :=
    add_nonneg (mul_nonneg hc (hd0 m)) (mul_nonneg hA (Lib.c3w_nonneg n m))
  have hdom : Summable (fun m : ℤ => (2*c^2)*d m^2+(2*A^2)*Lib.c3w n m^2) :=
    (hds.mul_left (2*c^2)).add ((Lib.summable_c3w_sq n).mul_left (2*A^2))
  have hsq (m : ℤ) : b m^2 ≤ (2*c^2)*d m^2+(2*A^2)*Lib.c3w n m^2 := by
    have hs := add_sq_le (a := c*d m) (b := A*Lib.c3w n m)
    simpa only [b,mul_pow,mul_add,mul_assoc] using hs
  have hbs : Summable (fun m : ℤ => b m^2) :=
    hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  refine ⟨b,hb0,hbs,?_,?_⟩
  · apply (hbs.tsum_le_tsum hsq hdom).trans
    rw [(hds.mul_left (2*c^2)).tsum_add
      ((Lib.summable_c3w_sq n).mul_left (2*A^2)),tsum_mul_left,tsum_mul_left,Lib.tsum_c3w_sq]
    exact add_le_add (mul_le_mul_of_nonneg_left hdB (by positivity)) le_rfl
  · intro m hnm z hz
    have hzOwn : z ∈ closedBall (C m) (R m) :=
      ball_subset_closedBall (((hspec φ hφ.2.2).1 m).1 hz)
    have hden := (p2OwnSigma_denominator38 C R c Ng hgeom n m hnm s hσ z hzOwn).1
    have hp := a5OwnClosedBall_omittedDomain38 φ (hUdW hφ.1) C R hfam m z hzOwn
    refine ⟨(angleRegularFactor_spectral_hasDerivAt38 n m (φ,s) z hp hden).differentiableAt,?_⟩
    have hder := (hdpoint m z hz).2
    have hval := hh φ hφ.2.1 s hs.2 m z hz
    have hcoef : 0 ≤ c^2/|((n-m : ℤ) : ℝ)| := by positivity
    calc
      _ ≤ c*‖deriv (fun w => p2OmittedRatio38 m ((φ,s),w)) z‖+
          (c^2/|((n-m : ℤ) : ℝ)|)*‖p2OmittedRatio38 m ((φ,s),z)‖ :=
        angleRegularFactor_weighted_deriv_bound38 φ (hUdW hφ.1) C R c Ng hgeom
          (hspec φ hφ.2.2) n m hnm s hσ z hzOwn
      _ ≤ c*d m+(c^2/|((n-m : ℤ) : ℝ)|)*H :=
        add_le_add (mul_le_mul_of_nonneg_left hder hc)
          (mul_le_mul_of_nonneg_left hval hcoef)
      _ = b m := by
        dsimp only [b,A,Lib.c3w]
        rw [Int.cast_sub,abs_sub_comm (n : ℝ) (m : ℝ)]
        ring

end
end NlsGge.GK38
