import CameraCalibration.Basic
import CameraCalibration.Gram

open Matrix

lemma equal_under_scalar_mul {K K' : Camera} (c : ℝ)
(h : K'.Uᵀ * K'.U = c • (K.Uᵀ * K.U)) :
 K.U = K'.U := by
  sorry
