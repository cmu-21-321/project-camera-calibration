import CameraCalibration.Basic
import CameraCalibration.Gram

theorem consistent_satisfies (h : ConsistentHomographyPair K H) : Satisfies (K.U.transpose * K.U) H := by
  obtain ⟨s, _, r₁, r₂, t, h0, h1, h2, _⟩ := h
  constructor
  · rw [gram_dot, h1, h2]
    simp [h0.dot_first_second]
  · simp [gram_dot, h1, h2]
    simp [h0.norm_first, h0.norm_second]
