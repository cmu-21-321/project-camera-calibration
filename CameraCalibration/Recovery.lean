import CameraCalibration.Basic
import CameraCalibration.Gram
import CameraCalibration.Params

open Matrix

lemma equal_under_scalar_mul {K K' : Camera} (c : ℝ)
(h : K'.Uᵀ * K'.U = c • (K.Uᵀ * K.U)) :
 K.U = K'.U := by

  rw [gram_eq, gram_eq] at h
  have h00 : K'.a^2 = c • K.a^2 := congrFun (congrFun h 0) 0
  have h01 : K'.a * K'.b = c • (K.a * K.b) := congrFun (congrFun h 0) 1
  have h02 : K'.a * K'.c = c • (K.a * K.c) := congrFun (congrFun h 0) 2
  have h11 : K'.b^2 + K'.d^2 = c • (K.b^2 + K.d^2) := congrFun (congrFun h 1) 1
  have h21 : K'.b * K'.c + K'.d * K'.e = c • (K.b * K.c + K.d * K.e) := congrFun (congrFun h 2) 1
  have h22 : K'.c ^ 2 + K'.e ^ 2 + 1 = c • (K.c ^ 2 + K.e ^ 2 + 1):= congrFun (congrFun h 2) 2

  obtain ⟨ha, hb, hc, hd, he⟩ := params_unique K.ha K.hd K'.ha K'.hd h00 h01 h02 h11 h21 h22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Camera.U, ha, hb, hc, hd, he]
