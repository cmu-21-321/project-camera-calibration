/-
Copyright (c) 2026 TODO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TODO
-/
module

public import CameraCalibration.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.LinearCombination

/-!
# TODO: title

TODO: one-paragraph summary of this file.

## Main definitions

* `CameraCalibration.VanishesOn`: TODO

## Main results

* `CameraCalibration.eq_of_vanishesOn_sub_smul_one`: TODO
* `CameraCalibration.eq_zero_of_vanishesOn_three`: TODO
-/

@[expose] public section

open Matrix

namespace CameraCalibration

-- all vectors perpendicular to the normal of the plane
-- rw r₁ᵀ D r₂ = 0 via h_1^T B h_2 = 0 =>
-- (s A r_1)^T B (s A r_2) = 0 =>
-- r_1^T A^T B A r_2 = 0
-- D = A^T B A
-- => r₁ᵀ D r₂
/-- TODO -/
def VanishesOn (D : M3) (n : V3) : Prop :=
  ∀ v : V3, v ⬝ᵥ n = 0 → v ⬝ᵥ (D *ᵥ v) = 0

private lemma cross_dot_cross_ne_zero {v w : V3} (h : v ⨯₃ w ≠ 0) :
    (v ⨯₃ w) ⬝ᵥ (v ⨯₃ w) ≠ 0 := by
  simp [dotProduct_self_eq_zero, h]

private lemma bilin_zero_of_vanishesOn {D : M3} {n x y : V3} (hD : D.IsSymm)
    (hv : VanishesOn D n) (hx : x ⬝ᵥ n = 0) (hy : y ⬝ᵥ n = 0) :
    x ⬝ᵥ (D *ᵥ y) = 0 := by
  have hxy : (x + y) ⬝ᵥ n = 0 := by
    simp [add_dotProduct, hx, hy]
  have hsum := hv (x + y) hxy
  have hxx := hv x hx
  have hyy := hv y hy
  simp only [mulVec_add, add_dotProduct, dotProduct_add, hxx, hyy] at hsum
  have hswap : y ⬝ᵥ (D *ᵥ x) = x ⬝ᵥ (D *ᵥ y) :=
    hD.dotProduct_mulVec_comm
  linarith

lemma mem_span_of_perp {r₁ r₂ x : V3} (hr : Orthonormal ℝ ![WithLp.toLp 2 r₁, WithLp.toLp 2 r₂])
    (hx : x ⬝ᵥ (r₁ ⨯₃ r₂) = 0) :
    x = (x ⬝ᵥ r₁) • r₁ + (x ⬝ᵥ r₂) • r₂ := by
  obtain ⟨h11, h22, h12⟩ := dotProduct_eq_of_orthonormal hr
  set a := x ⬝ᵥ r₁
  set b := x ⬝ᵥ r₂
  set y := x - a • r₁ - b • r₂ with hy
  have hy1 : r₁ ⬝ᵥ y = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, h12,
      h11, mul_one, smul_eq_mul, mul_zero, sub_zero]
    ring
  have hy2 : r₂ ⬝ᵥ y = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, h12,
      h22, smul_eq_mul, mul_zero, sub_zero]
    ring
  have hy0 : (r₁ ⨯₃ r₂) ⬝ᵥ y = 0 := by
    simp only [hy, dotProduct_comm, sub_dotProduct, hx, smul_dotProduct, dot_self_cross,
      smul_eq_mul, mul_zero, sub_self, dot_cross_self]
  have hn1 : (r₁ ⨯₃ r₂) ⬝ᵥ (r₁ ⨯₃ r₂) = 1 := by
    rw [cross_dot_cross, h12, h11, h22]
    ring
  have hc0 : r₁ ⨯₃ r₂ ⨯₃ y = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hy1, hy2, zero_smul, zero_smul]
    ring
  have hyy : y ⬝ᵥ y = 0 := by
    have hC := cross_dot_cross (r₁ ⨯₃ r₂) y (r₁ ⨯₃ r₂) y
    rw [hc0, hn1, hy0] at hC
    rw [zero_dotProduct, one_mul, zero_mul, sub_zero] at hC
    exact hC.symm
  have hyz : y = 0 := dotProduct_star_self_eq_zero.mp hyy
  rwa [hy, sub_sub, sub_eq_zero] at hyz

lemma dotProduct_sub_smul_one_mulVec_self_eq_zero {E : M3} {r₁ r₂ x : V3}
    (hr : Orthonormal ℝ ![WithLp.toLp 2 r₁, WithLp.toLp 2 r₂]) (hE : E.IsSymm)
    (c12 : r₁ ⬝ᵥ (E *ᵥ r₂) = 0)
    (c11 : r₁ ⬝ᵥ (E *ᵥ r₁) = r₂ ⬝ᵥ (E *ᵥ r₂))
    (hx : x = (x ⬝ᵥ r₁) • r₁ + (x ⬝ᵥ r₂) • r₂) :
    x ⬝ᵥ ((E - (r₁ ⬝ᵥ (E *ᵥ r₁)) • 1) *ᵥ x) = 0 := by
  obtain ⟨h11, h22, h12⟩ := dotProduct_eq_of_orthonormal hr
  set a := x ⬝ᵥ r₁
  set b := x ⬝ᵥ r₂
  set μ := r₁ ⬝ᵥ (E *ᵥ r₁) with hμ
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_mulVec, dotProduct_smul, smul_eq_mul]
  have hxx : x ⬝ᵥ x = a ^ 2 + b ^ 2 := by
    simp only [hx, dotProduct_add, dotProduct_smul,
      h22, h12, h11, dotProduct_comm,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hxE : x ⬝ᵥ (E *ᵥ x) = a ^ 2 * μ + b ^ 2 * μ := by
    rw [hx, hμ]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [← c11, hE.dotProduct_mulVec_comm (x := r₂) (y := r₁), c12]
    simp only [mul_zero, add_zero, zero_add]
    ring
  rw [← dotProduct_mulVec, (hE.dotProduct_mulVec_comm (x := x) (y := x)).symm, hxE, hxx]
  ring

lemma eq_of_vanishesOn_sub_smul_one {D : M3} {n₁ n₂ : V3} {μ₁ μ₂ : ℝ} (h₁₂ : n₁ ⨯₃ n₂ ≠ 0)
    (v₁ : VanishesOn (D - μ₁ • 1) n₁) (v₂ : VanishesOn (D - μ₂ • 1) n₂) :
    μ₁ = μ₂ := by
  set w := n₁ ⨯₃ n₂
  have hP1 : w ⬝ᵥ n₁ = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross n₁ n₂
  have hP2 : w ⬝ᵥ n₂ = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self n₁ n₂
  specialize v₁ _ hP1
  specialize v₂ _ hP2
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_mulVec, dotProduct_smul, smul_eq_mul] at v₁ v₂
  have hwwn0 : w ⬝ᵥ w ≠ 0 := by simp [ne_eq, dotProduct_self_eq_zero, h₁₂]
  have e1 : (μ₁ - μ₂) * (w ⬝ᵥ w) = 0 := by linarith
  have e2 : μ₁ - μ₂ = 0 := (mul_eq_zero_iff_right hwwn0).mp e1
  linarith

private lemma cross_dot_self_smul_eq (n₁ n₂ x : V3) :
    ((n₁ ⨯₃ n₂) ⬝ᵥ (n₁ ⨯₃ n₂)) • x =
      (x ⬝ᵥ n₁) • (n₂ ⨯₃ (n₁ ⨯₃ n₂)) - (x ⬝ᵥ n₂) • (n₁ ⨯₃ (n₁ ⨯₃ n₂))
        + (x ⬝ᵥ (n₁ ⨯₃ n₂)) • (n₁ ⨯₃ n₂) := by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
    · dsimp
      ring

-- If a symmetric `D` vanishes on the planes `n₁ᗮ` and `n₂ᗮ`, then up to the factor
-- `‖n₁ × n₂‖⁴` its bilinear form is determined by the single number
-- `(n₁ × (n₁ × n₂)) ⬝ᵥ D (n₂ × (n₁ × n₂))`.
private lemma smul_bilin_eq_of_vanishesOn_two {D : M3} {n₁ n₂ : V3} (hD : D.IsSymm)
    (v₁ : VanishesOn D n₁) (v₂ : VanishesOn D n₂) (x y : V3) :
    ((n₁ ⨯₃ n₂) ⬝ᵥ (n₁ ⨯₃ n₂)) * ((n₁ ⨯₃ n₂) ⬝ᵥ (n₁ ⨯₃ n₂)) * (x ⬝ᵥ (D *ᵥ y)) =
      -((n₁ ⨯₃ (n₁ ⨯₃ n₂)) ⬝ᵥ (D *ᵥ (n₂ ⨯₃ (n₁ ⨯₃ n₂)))) *
        ((x ⬝ᵥ n₁) * (y ⬝ᵥ n₂) + (x ⬝ᵥ n₂) * (y ⬝ᵥ n₁)) := by
  set w := n₁ ⨯₃ n₂
  set a := n₁ ⨯₃ w
  set b := n₂ ⨯₃ w
  set s := w ⬝ᵥ w
  set κ := a ⬝ᵥ (D *ᵥ b) with hκ
  have hwn1 : w ⬝ᵥ n₁ = 0 := by rw [dotProduct_comm, dot_self_cross]
  have hwn2 : w ⬝ᵥ n₂ = 0 := by rw [dotProduct_comm, dot_cross_self]
  have han1 : a ⬝ᵥ n₁ = 0 := by rw [dotProduct_comm, dot_self_cross]
  have hbn2 : b ⬝ᵥ n₂ = 0 := by rw [dotProduct_comm, dot_self_cross]
  have h1wa := bilin_zero_of_vanishesOn hD v₁ hwn1 han1
  have h1aw := bilin_zero_of_vanishesOn hD v₁ han1 hwn1
  have h1aa := bilin_zero_of_vanishesOn hD v₁ han1 han1
  have h1ww := bilin_zero_of_vanishesOn hD v₁ hwn1 hwn1
  have h2wb := bilin_zero_of_vanishesOn hD v₂ hwn2 hbn2
  have h2bw := bilin_zero_of_vanishesOn hD v₂ hbn2 hwn2
  have h2ww := bilin_zero_of_vanishesOn hD v₂ hwn2 hwn2
  have h2bb := bilin_zero_of_vanishesOn hD v₂ hbn2 hbn2
  have κSymm : b ⬝ᵥ (D *ᵥ a) = κ := hD.dotProduct_mulVec_comm (x := b) (y := a)
  have : s * s * (x ⬝ᵥ (D *ᵥ y)) = (s • x) ⬝ᵥ (D *ᵥ (s • y)) := by
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hx : s • x = (x ⬝ᵥ n₁) • b - (x ⬝ᵥ n₂) • a + (x ⬝ᵥ w) • w :=
    cross_dot_self_smul_eq n₁ n₂ x
  have hy : s • y = (y ⬝ᵥ n₁) • b - (y ⬝ᵥ n₂) • a + (y ⬝ᵥ w) • w :=
    cross_dot_self_smul_eq n₁ n₂ y
  rw [this, hx, hy]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    h1wa, h1aw, h1aa, h1ww, h2wb, h2bw, h2bb, κSymm, ← hκ]
  ring

-- If `κ (x ⬝ᵥ n₁) (x ⬝ᵥ n₂)` vanishes on the plane `n₃ᗮ` and neither `n₁` nor `n₂` is
-- parallel to `n₃`, then `κ = 0`: test on `u = n₃ × (n₁ × n₃)`, `v = n₃ × (n₂ × n₃)` and `u + v`.
private lemma eq_zero_of_forall_dot_mul_dot_eq_zero {κ : ℝ} {n₁ n₂ n₃ : V3}
    (h₁₃ : n₁ ⨯₃ n₃ ≠ 0) (h₂₃ : n₂ ⨯₃ n₃ ≠ 0)
    (hP : ∀ x : V3, x ⬝ᵥ n₃ = 0 → κ * ((x ⬝ᵥ n₁) * (x ⬝ᵥ n₂)) = 0) :
    κ = 0 := by
  set u := n₃ ⨯₃ (n₁ ⨯₃ n₃) with hu
  set v := n₃ ⨯₃ (n₂ ⨯₃ n₃) with hv
  have hu3 : u ⬝ᵥ n₃ = 0 := by rw [dotProduct_comm, dot_self_cross]
  have hv3 : v ⬝ᵥ n₃ = 0 := by rw [dotProduct_comm, dot_self_cross]
  have hu1 : u ⬝ᵥ n₁ ≠ 0 := by
    rw [hu, dotProduct_comm, triple_product_permutation, triple_product_permutation]
    simp [dotProduct_self_eq_zero, h₁₃]
  have hv2 : v ⬝ᵥ n₂ ≠ 0 := by
    rw [hv, dotProduct_comm, triple_product_permutation, triple_product_permutation]
    simp [dotProduct_self_eq_zero, h₂₃]
  by_contra hnκ
  have eu := hP u hu3
  have ev := hP v hv3
  have euv := hP (u + v) (by rw [add_dotProduct, hu3, hv3, zero_add])
  have hu2 : u ⬝ᵥ n₂ = 0 := by simpa [hnκ, hu1] using eu
  have hv1 : v ⬝ᵥ n₁ = 0 := by simpa [hnκ, hv2] using ev
  rw [add_dotProduct, add_dotProduct, hu2, hv1, add_zero, zero_add] at euv
  exact mul_ne_zero hnκ (mul_ne_zero hu1 hv2) euv

private lemma eq_zero_of_forall_dotProduct_mulVec_eq_zero {D : M3}
    (h : ∀ x y : V3, x ⬝ᵥ (D *ᵥ y) = 0) : D = 0 := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single_one, single_one_dotProduct] using hij

/-- TODO -/
theorem eq_zero_of_vanishesOn_three {D : M3} {n₁ n₂ n₃ : V3} (hD : D.IsSymm)
    (h₁₂ : n₁ ⨯₃ n₂ ≠ 0) (h₁₃ : n₁ ⨯₃ n₃ ≠ 0) (h₂₃ : n₂ ⨯₃ n₃ ≠ 0)
    (v₁ : VanishesOn D n₁) (v₂ : VanishesOn D n₂) (v₃ : VanishesOn D n₃) :
    D = 0 := by
  set w := n₁ ⨯₃ n₂
  set s := w ⬝ᵥ w
  set κ := (n₁ ⨯₃ w) ⬝ᵥ (D *ᵥ (n₂ ⨯₃ w))
  have h : ∀ x y : V3, s * s * (x ⬝ᵥ (D *ᵥ y)) =
      -κ * ((x ⬝ᵥ n₁) * (y ⬝ᵥ n₂) + (x ⬝ᵥ n₂) * (y ⬝ᵥ n₁)) :=
    smul_bilin_eq_of_vanishesOn_two hD v₁ v₂
  have hP3 : ∀ x : V3, x ⬝ᵥ n₃ = 0 → κ * ((x ⬝ᵥ n₁) * (x ⬝ᵥ n₂)) = 0 := by
    intro x hx
    have h0 := v₃ x hx
    have hk := h x x
    linear_combination (1 / 2) * hk - (s * s / 2) * h0
  have hκ0 : κ = 0 := eq_zero_of_forall_dot_mul_dot_eq_zero h₁₃ h₂₃ hP3
  have hs : s ≠ 0 := cross_dot_cross_ne_zero (v := n₁) (w := n₂) h₁₂
  refine eq_zero_of_forall_dotProduct_mulVec_eq_zero fun x y => ?_
  have hk := h x y
  rw [hκ0, neg_zero, zero_mul] at hk
  rcases mul_eq_zero.mp hk with h' | h'
  · exact absurd h' (mul_ne_zero hs hs)
  · exact h'

end CameraCalibration
