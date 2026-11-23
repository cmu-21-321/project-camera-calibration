/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import CameraCalibration.Gram

/-!
# Satisfies

This file contains the `consistent_satisfies` theorem which provides a proof
that given a consistent homography for a camera that `B = UᵀU` meets our `Satisfies`
definition as a valid solution to the homography consistent with `K`

## Main results

* `CameraCalibration.consistent_satisfies`: given a camera and consistent homography,
the gram of U is a valid solution to the problem
-/

public section

open Matrix

namespace CameraCalibration

theorem consistent_satisfies {K : Camera} {H : M3} {s : ℝ} {r₁ r₂ : V3}
    (h : ConsistentHomographyPair K H s r₁ r₂) : Satisfies (K.Uᵀ * K.U) H := by
  obtain ⟨_, h0, h1, h2⟩ := h
  obtain ⟨h11, h22, h12⟩ := dotProduct_eq_of_orthonormal h0
  constructor
  · rw [gram_dot, h1, h2]
    simp [h12]
  · simp [gram_dot, h1, h2, h11, h22]

end CameraCalibration
