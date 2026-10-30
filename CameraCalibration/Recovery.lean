import CameraCalibration.Basic
import CameraCalibration.Gram

open Matrix

lemma equal_under_scalar_mul {K K' : Camera} (c : ℝ)
(h : K'.Uᵀ * K'.U = c • (K.Uᵀ * K.U)) :
 K.U = K'.U := by

  rw [gram_eq, gram_eq] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h20 := congrFun (congrFun h 2) 0
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2

  sorry
