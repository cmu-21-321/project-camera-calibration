/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import CameraCalibration.Recovery
public import CameraCalibration.Satisfies
public import CameraCalibration.Unique

/-!
# Main

This file contains the theorem we directly prove: `zhang_nonparallel_uniqueness` and
its corollary which is Zhang's actual assertion: `zhang_intrinsics_unique`.
They both take in all the constraints and definitions defined in the problem and use the key
`eq_smul_gram` lemma in `Unique.lean` which proves `B = μUᵀU` then uses
`U_eq_of_gram_eq_smul` to derive that then `U = U'`. While our representation is the inverse of the
intrinsics matrix then `zhang_intrinsics_unique` proves that the inverses must also be equivalent
which is the theorem we want to prove.

## Main results

* `CameraCalibration.zhang_nonparallel_uniqueness`: proves we can determine the U's are equal
 given 3 non-parallel planes with corresponding homographies are equal under a scalar multiplication
* `CameraCalibration.zhang_intrinsics_unique`: proves that given the inverse intrinsics are equal
  then so are the intrinsics
given the same hypotheses as `zhang_nonparallel_uniqueness` which it uses as a lemma

## References

* “A Flexible New Technique for Camera Calibration” (2000)
-/

public section

open Matrix

namespace CameraCalibration

/-- For any two sets of camera parameters, given 3 non-parallel planes represented by consistent
 camera homography pairs, then the camera intrinsics inverses are the same. -/
theorem zhang_nonparallel_uniqueness {K K' : Camera} {H₁ H₂ H₃ : M3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K H s r₁ r₂)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K' H s r₁ r₂)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0) (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.U = K'.U := by
    have hB := gram_symm K'.U
    have hs : ∀ H ∈ [H₁, H₂, H₃], Satisfies (K'.Uᵀ * K'.U) H := by
      intro H hH
      obtain ⟨μ, _, _, hμ⟩ := h' H hH
      exact consistent_satisfies hμ
    obtain ⟨μ, hμ⟩ := eq_smul_gram hB h hs h₁₂ h₁₃ h₂₃
    exact U_eq_of_gram_eq_smul μ hμ

/-- For any two sets of camera parameters, given 3 non-parallel planes represented by consistent
 camera homography pairs, then the camera intrinsics are the same. -/
theorem zhang_intrinsics_unique {K K' : Camera} {H₁ H₂ H₃ : M3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K H s r₁ r₂)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K' H s r₁ r₂)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0) (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.U⁻¹ = K'.U⁻¹ := by
  have hK : K.U = K'.U := zhang_nonparallel_uniqueness h h' h₁₂ h₁₃ h₂₃
  calc
    K.U⁻¹ = K.U⁻¹ * (K'.U * K'.U⁻¹) := by rw [K'.U_mul_inv, mul_one]
    _ = (K.U⁻¹ * K'.U) * K'.U⁻¹ := by rw [mul_assoc]
    _ = (K.U⁻¹ * K.U) * K'.U⁻¹ := by rw [hK]
    _ = K'.U⁻¹ := by rw [K.inv_mul_U, one_mul]

end CameraCalibration
