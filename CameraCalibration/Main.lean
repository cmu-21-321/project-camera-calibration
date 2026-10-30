import CameraCalibration.Basic
import CameraCalibration.Recovery

open Matrix


theorem zhang_three_view_uniqueness
(hUnique : UniqueToScaleFactor [H₁, H₂, H₃])
(h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
(h' : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K' H)
: K.U = K'.U := by
  let B : M3 := K.Uᵀ * K.U
  let B' : M3 := K'.Uᵀ * K'.U
  obtain ⟨s, hs⟩ := hUnique B B' (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
  exact equal_under_scalar_mul s hs
