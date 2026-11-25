import NlsGge.Schur.ActualSchurOwnModeVariation38V1
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange

                                                                                                                                                                                                                                                                                                               
                                                                                                              
                                                                                                           
                                                     
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.S
noncomputable section

def ownMode (n : ℤ) :=
  NlsGge.Schur.actualOwnModeVariation38 n

def P (n : ℤ) : NlsGge.Schur.ParityPair n →L[ℂ] NlsGge.Schur.ParityPair n :=
  NlsGge.Schur.resonantParityPair n

def Q (n : ℤ) : NlsGge.Schur.ParityPair n →L[ℂ] NlsGge.Schur.ParityPair n :=
  NlsGge.Schur.freeResolventComplementaryProjectionTransported n

theorem ownMode_cross_zero (n : ℤ) : Q n*ownMode n*P n=0 ∧ P n*ownMode n*Q n=0 := by
  refine ⟨?_, ?_⟩
  · exact NlsGge.Schur.actualOwnModeVariation38_Q_H_P n
  · exact NlsGge.Schur.actualOwnModeVariation38_P_H_Q n

