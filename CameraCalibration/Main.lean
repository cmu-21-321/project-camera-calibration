import CameraCalibration.Basic
import CameraCalibration.Satisfies
import CameraCalibration.Recovery

open Matrix

theorem zhang_three_view_uniqueness
(hUnique : UniqueToScaleFactor [H₁, H₂, H₃])
(h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
(h' : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K' H)
: K.U = K'.U := by
  let B : M3 := K.Uᵀ * K.U
  let B' : M3 := K'.Uᵀ * K'.U
  obtain ⟨s, hs⟩ := hUnique B B'
  (gram_symm K.U).symm
  (gram_symm K'.U).symm
  (fun H hH => consistent_satisfies (h H hH))
  (fun H hH => consistent_satisfies (h' H hH))
  (gram_ne_zero K)
  exact equal_under_scalar_mul s hs
