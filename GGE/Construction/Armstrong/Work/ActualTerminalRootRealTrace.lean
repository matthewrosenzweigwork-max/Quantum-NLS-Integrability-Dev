import Armstrong.Work.CartesianTerminalRootSpec
import NlsGge.GK38.DirichletRealGapIndex
import Mathlib.Analysis.Complex.Order

/-!
# Actual terminal root on the real slice

SPECULATIVE_PARENT_UNACCEPTED. RT-H-007 is the initial pointwise
`realTracePrereq` subclaim. The literal terminal root squares to the own
quadratic. Actual real Dirichlet interlacing makes this square nonpositive,
which forces the root to be purely imaginary. No square-root sign, gap
nonvanishing, or terminal-interior assumption is used. The statement includes
every real collapsed gap and both terminal tips. Coordinate conjugation,
weighted correction reality, and source beta reality remain separate work.
-/
set_option autoImplicit false
open NlsGge.Pilot
open scoped ComplexOrder
namespace NlsGge.GK38
noncomputable section

theorem gk16_terminal_root_real_trace38 (u : PhysicalL2) (n : ℤ) :
    (gk16TerminalRoot38 n (realSlice u)).re = 0 := by
  have hmu := gkMu_mem_gap38 u n
  have hnonpos :
      (gkMu u n-NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n) *
        (gkMu u n-NlsGge.SpectralFoundations.actualGapUpperAllE02_38 u n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hmu.1) (sub_nonpos.mpr hmu.2)
  apply Complex.sq_nonpos_iff.mp
  rw [gk16_terminal_root_sq38 n (realSlice u) (realSlice_mem_gkW u),
    muSeq_eq_gkMu38 u n, (lamPlus_real u n).2, (lamPlus_real u n).1]
  exact_mod_cast hnonpos

end
end NlsGge.GK38
