import CameraCalibration.Basic

open Matrix

-- all vectors perpendicular to the normal of the plane
-- rw r₁ᵀ D r₂ = 0 via h_1^T B h_2 = 0 =>
-- (s A r_1)^T B (s A r_2) = 0 =>
-- r_1^T A^T B A r_2 = 0
-- D = A^T B A
-- => r₁ᵀ D r₂
def vanishes_on (D : M3) (n : V3) : Prop :=
  ∀v : V3, dotProduct v n = 0 → dotProduct v (D *ᵥ v) = 0

lemma conj_symm {B : M3} {K : Camera} (hB : B = Bᵀ) :
  (K.Aᵀ * B * K.A)ᵀ = K.Aᵀ * B * K.A := by
  simp [hB.symm, transpose_mul, mul_assoc]

lemma view_constraints {K : Camera} {H : HomographyM3} {B : M3} {s : ℝ} {r₁ r₂ : V3}
    (hs0 : s ≠ 0)
    (h1 : K.U *ᵥ H.h₁ = s • r₁)
    (h2 : K.U *ᵥ H.h₂ = s • r₂)
    (hs : Satisfies B H) :
    dotProduct r₁ ((K.Aᵀ * B * K.A) *ᵥ r₂) = 0 ∧
    dotProduct r₁ ((K.Aᵀ * B * K.A) *ᵥ r₁) = dotProduct r₂ ((K.Aᵀ * B * K.A) *ᵥ r₂) := by
  obtain ⟨c1, c2⟩ := hs
  rw [h1, h2] at c1 c2
  constructor
  ·
