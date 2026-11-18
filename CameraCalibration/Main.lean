import CameraCalibration.Basic
import CameraCalibration.Satisfies
import CameraCalibration.Recovery

open Matrix

theorem zhang_three_view_uniqueness
(hUnique : UniqueToScaleFactor [H₁, H₂, H₃])
(h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
(h' : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K' H)
: K.U = K'.U := by
  let B : M3 := K.Uᵀ * K.U
  let B' : M3 := K'.Uᵀ * K'.U
  obtain ⟨s, hs⟩ := hUnique B B'
    (gram_symm K.U).symm
    (gram_symm K'.U).symm
    (fun H hH => consistent_satisfies (h H hH))
    (fun H hH => consistent_satisfies (h' H hH))
    (gram_ne_zero K)
  exact equal_under_scalar_mul s hs

theorem zhang_nonparallel_uniqueness {K K' : Camera} {H₁ H₂ H₃ : HomographyM3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K' H)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0)
    (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.U = K'.U :=
  zhang_three_view_uniqueness (unique_of_nonparallel h h₁₂ h₁₃ h₂₃) h h'

theorem zhang_intrinsics_unique {K K' : Camera} {H₁ H₂ H₃ : HomographyM3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K' H)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0)
    (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.A = K'.A := by
  have hK : K.U = K'.U := zhang_nonparallel_uniqueness h h' h₁₂ h₁₃ h₂₃
  calc
    K.A = K.A * (K'.U * K'.A) := by rw [K'.U_mul_A, mul_one]
    _ = (K.A * K'.U) * K'.A := by rw [mul_assoc]
    _ = (K.A * K.U) * K'.A := by rw [hK]
    _ = K'.A := by rw [K.A_mul_U, one_mul]
