/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import CameraCalibration.Basic
public import Mathlib.Algebra.Order.Star.Real

/-!
# Gram

This file contains a few helping lemmas for matrix products of the form
`UᵀU` along with some that are specific to the structure of the camera-defined matrices
which appear often in this formalization.

## Main results

* `CameraCalibration.gram_eq`: proves the matrix result of the inverse camera matrix transpose
with itself
-/

public section

open Matrix

namespace CameraCalibration

-- in the paper have B=A⁻ᵀA⁻¹=UᵀU
lemma gram_eq (K : Camera) : K.Uᵀ * K.U =
    !![K.a ^ 2, K.a * K.b, K.a * K.c;
      K.a * K.b, K.b ^ 2 + K.d ^ 2, K.b * K.c + K.e * K.d;
      K.a * K.c, K.b * K.c + K.d * K.e, K.c ^ 2 + K.e ^ 2 + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Camera.U, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

lemma gram_symm (U : M3) : (Uᵀ * U)ᵀ = Uᵀ * U := by
  simp only [transpose_mul, transpose_transpose]

lemma gram_ne_zero (K : Camera) : (K.Uᵀ * K.U) ≠ 0 := by
  intro h
  have ha := K.ha
  have hM := gram_eq K
  rw [hM] at h
  have hA2 : K.a ^ 2 = 0 := congr_fun (congr_fun h 0) 0
  nlinarith

lemma gram_dot (U : M3) (u v : V3) :
    u ⬝ᵥ ((Uᵀ * U) *ᵥ v) = (U *ᵥ u) ⬝ᵥ (U *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

end CameraCalibration
