/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/
module

public import CameraCalibration.Gram

/-!
# TODO: title

TODO: one-paragraph summary of this file.

## Main results

* `CameraCalibration.consistent_satisfies`: TODO
-/

public section

open Matrix

namespace CameraCalibration

theorem consistent_satisfies {K : Camera} {H : M3} {s : ℝ} {r₁ r₂ : V3}
    (h : ConsistentHomographyPair K H s r₁ r₂) : Satisfies (K.Uᵀ * K.U) H := by
  obtain ⟨h11, h22, h12⟩ := dotProduct_eq_of_orthonormal h.orthonormal
  constructor
  · rw [gram_dot, h.mulVec_col_zero, h.mulVec_col_one]
    simp [h12]
  · simp [gram_dot, h.mulVec_col_zero, h.mulVec_col_one, h11, h22]

end CameraCalibration
