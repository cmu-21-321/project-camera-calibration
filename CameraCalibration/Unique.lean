/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import CameraCalibration.Plane

/-!
# Unique

This file is all about proving the important `eq_smul_gram` theorem which
tells us that given our set of consistent homography pairs for our 3 non-parallel
planes, our symmetric solution matrix `B` can be written as a scalar multiplication
of our inverse camera intrinsic matrices so `B = μUᵀU`. Other private lemmas exist
to help prove this result.

## Main results

* `CameraCalibration.eq_smul_gram`: proves that given our problem setup and solution `B`
we can write it using the camera matrices as described above.
-/

public section

open Matrix

namespace CameraCalibration

private lemma dotProduct_conj_mulVec (A B : M3) (u v : V3) :
    u ⬝ᵥ ((Aᵀ * B * A) *ᵥ v) = (A *ᵥ u) ⬝ᵥ (B *ᵥ (A *ᵥ v)) := by
  simp only [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

private lemma isSymm_conj {B : M3} {K : Camera} (hB : B.IsSymm) :
    ((K.U⁻¹)ᵀ * B * K.U⁻¹).IsSymm := by
  change ((K.U⁻¹)ᵀ * B * K.U⁻¹)ᵀ = (K.U⁻¹)ᵀ * B * K.U⁻¹
  simp [hB.eq, transpose_mul, mul_assoc]

private lemma conj_constraints_of_satisfies {K : Camera} {H : M3} {B : M3} {s : ℝ}
    {r₁ r₂ : V3} (hs0 : s ≠ 0) (h1 : K.U *ᵥ Hᵀ 0 = s • r₁) (h2 : K.U *ᵥ Hᵀ 1 = s • r₂)
    (hs : Satisfies B H) :
    r₁ ⬝ᵥ (((K.U⁻¹)ᵀ * B * K.U⁻¹) *ᵥ r₂) = 0 ∧
      r₁ ⬝ᵥ (((K.U⁻¹)ᵀ * B * K.U⁻¹) *ᵥ r₁) = r₂ ⬝ᵥ (((K.U⁻¹)ᵀ * B * K.U⁻¹) *ᵥ r₂) := by
  obtain ⟨c1, c2⟩ := hs
  have e1 : Hᵀ 0 = s • (K.U⁻¹ *ᵥ r₁) := by
    have := congrArg (K.U⁻¹ *ᵥ ·) h1
    simp only [mulVec_mulVec, K.inv_mul_U, one_mulVec, mulVec_smul] at this
    assumption
  have e2 : Hᵀ 1 = s • (K.U⁻¹ *ᵥ r₂) := by
    have := congrArg (K.U⁻¹ *ᵥ ·) h2
    simp only [mulVec_mulVec, K.inv_mul_U, one_mulVec, mulVec_smul] at this
    assumption
  simp only [dotProduct_conj_mulVec]
  constructor
  · rw [e1, e2] at c1
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at c1
    simpa [hs0] using c1
  · rw [e1, e2] at c2
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at c2
    simpa [hs0] using c2

private lemma exists_vanishesOn_conj_sub_smul_one {K : Camera} {H B : M3} {s : ℝ} {r₁ r₂ : V3}
    (hB : B.IsSymm) (hc : ConsistentHomographyPair K H s r₁ r₂) (hs : Satisfies B H) :
    ∃ μ : ℝ, VanishesOn ((K.U⁻¹)ᵀ * B * K.U⁻¹ - μ • 1) (K.normal H) := by
  obtain ⟨hs0, hr, h1, h2⟩ := hc
  obtain ⟨c11, c12⟩ := conj_constraints_of_satisfies hs0 h1 h2 hs
  refine ⟨r₁ ⬝ᵥ (((K.U⁻¹)ᵀ * B * K.U⁻¹) *ᵥ r₁), ?_⟩
  intro x hx
  rw [K.normal_eq h1 h2, dotProduct_smul, smul_eq_mul] at hx
  have hx' := by simpa [hs0] using hx
  exact dotProduct_sub_smul_one_mulVec_self_eq_zero hr (isSymm_conj hB) c11 c12
    (mem_span_of_perp hr hx')

theorem eq_smul_gram {K : Camera} {H₁ H₂ H₃ : M3} {B : M3} (hB : B.IsSymm)
    (h : ∀ H ∈ [H₁, H₂, H₃], ∃ s r₁ r₂, ConsistentHomographyPair K H s r₁ r₂)
    (hs : ∀ H ∈ [H₁, H₂, H₃], Satisfies B H)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0) (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    ∃ μ : ℝ, B = μ • (K.Uᵀ * K.U) := by
  obtain ⟨_, _, _, hc₁⟩ := h H₁ (by simp)
  obtain ⟨_, _, _, hc₂⟩ := h H₂ (by simp)
  obtain ⟨_, _, _, hc₃⟩ := h H₃ (by simp)
  obtain ⟨μ₁, v₁⟩ := exists_vanishesOn_conj_sub_smul_one hB hc₁ (hs H₁ (by simp))
  obtain ⟨μ₂, v₂⟩ := exists_vanishesOn_conj_sub_smul_one hB hc₂ (hs H₂ (by simp))
  obtain ⟨μ₃, v₃⟩ := exists_vanishesOn_conj_sub_smul_one hB hc₃ (hs H₃ (by simp))
  have hμ₁μ₂ : μ₁ = μ₂ := eq_of_vanishesOn_sub_smul_one h₁₂ v₁ v₂
  have hμ₂μ₃ : μ₂ = μ₃ := eq_of_vanishesOn_sub_smul_one h₂₃ v₂ v₃
  have hμ₁μ₃ : μ₁ = μ₃ := hμ₁μ₂.trans hμ₂μ₃
  subst hμ₂μ₃ hμ₁μ₃
  have hS : ((K.U⁻¹)ᵀ * B * K.U⁻¹ - μ₁ • 1).IsSymm := (isSymm_conj hB).sub (isSymm_one.smul μ₁)
  have hE0 : ((K.U⁻¹)ᵀ * B * K.U⁻¹) - μ₁ • 1 = 0 :=
    eq_zero_of_vanishesOn_three hS h₁₂ h₁₃ h₂₃ v₁ v₂ v₃
  have hD : ((K.U⁻¹)ᵀ * B * K.U⁻¹) = μ₁ • 1 := sub_eq_zero.mp hE0
  use μ₁
  calc
    B = K.Uᵀ * ((K.U⁻¹)ᵀ * B * K.U⁻¹) * K.U := K.eq_conj B
    _ = μ₁ • (K.Uᵀ * K.U) := by simp [hD]

end CameraCalibration
