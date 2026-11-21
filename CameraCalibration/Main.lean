/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/
module

public import CameraCalibration.Recovery
public import CameraCalibration.Satisfies
public import CameraCalibration.Unique

/-!
# TODO: title

TODO: one-paragraph summary of this file.

## Main results

* `CameraCalibration.zhang_nonparallel_uniqueness`: TODO
* `CameraCalibration.zhang_intrinsics_unique`: TODO

## References

* TODO
-/

public section

open Matrix

namespace CameraCalibration

/-- TODO -/
theorem zhang_nonparallel_uniqueness {K K' : Camera} {H₁ H₂ H₃ : M3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K H s r₁ r₂)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K' H s r₁ r₂)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0) (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.U = K'.U := by
  -- `K'.Uᵀ * K'.U` satisfies the constraints of every view, so it is a multiple of `K.Uᵀ * K.U`
  obtain ⟨μ, hμ⟩ := eq_smul_gram (isSymm_transpose_mul_self K'.U) h
    (fun H hH => by obtain ⟨_, _, _, hc⟩ := h' H hH; exact consistent_satisfies hc) h₁₂ h₁₃ h₂₃
  exact U_eq_of_gram_eq_smul μ hμ

/-- TODO -/
theorem zhang_intrinsics_unique {K K' : Camera} {H₁ H₂ H₃ : M3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K H s r₁ r₂)
    (h' : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K' H s r₁ r₂)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0) (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    K.U⁻¹ = K'.U⁻¹ :=
  congrArg (·⁻¹) (zhang_nonparallel_uniqueness h h' h₁₂ h₁₃ h₂₃)

end CameraCalibration
