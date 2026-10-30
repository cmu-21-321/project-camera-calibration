import CameraCalibration.Basic

open Matrix

-- in the paper have B=A⁻ᵀA⁻¹=UᵀU
lemma gram_eq (K : Camera) : K.Uᵀ * K.U =
  !![K.a^2, K.a * K.b, K.a * K.c;
    K.a * K.b, K.b^2 + K.d^2, K.b * K.c + K.e * K.d;
    K.a * K.c, K.b * K.c + K.d * K.e, K.c^2 + K.e^2 + 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Camera.U, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring_nf

lemma gram_symm (U : M3) : (Uᵀ * U)ᵀ = Uᵀ * U := by
  simp only [transpose_mul, transpose_transpose]

lemma gram_ne_zero (K : Camera) : (K.Uᵀ * K.U) ≠ 0 := by
  intro h
  have ha := K.ha
  have hM := gram_eq K
  rw [hM] at h
  have hA2 : K.a^2 = 0 := congr_fun (congr_fun h 0) 0
  have hA2_nonneg : K.a^2 > 0 := by positivity
  linarith
