/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/
module

public import CameraCalibration.Basic
public import Mathlib.Algebra.Order.Star.Real

/-!
# TODO: title

TODO: one-paragraph summary of this file.

## Main results

* `CameraCalibration.gram_eq`: TODO
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

lemma gram_dot (U : M3) (u v : V3) :
    u ⬝ᵥ ((Uᵀ * U) *ᵥ v) = (U *ᵥ u) ⬝ᵥ (U *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

end CameraCalibration
