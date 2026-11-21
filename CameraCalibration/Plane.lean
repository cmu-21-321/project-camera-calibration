import CameraCalibration.Basic

open Matrix

-- all vectors perpendicular to the normal of the plane
-- rw r₁ᵀ D r₂ = 0 via h_1^T B h_2 = 0 =>
-- (s A r_1)^T B (s A r_2) = 0 =>
-- r_1^T A^T B A r_2 = 0
-- D = A^T B A
-- => r₁ᵀ D r₂
def VanishesOn (D : M3) (n : V3) : Prop :=
  ∀v : V3, dotProduct v n = 0 → dotProduct v (D *ᵥ v) = 0

lemma sub_smul_one_symm {E : M3} (μ : ℝ) (hE : Eᵀ = E) :
    (E - μ • 1)ᵀ = E - μ • 1 := by
  rw [transpose_sub, hE, transpose_smul, transpose_one]

lemma bilin_zero_of_vanishesOn {D : M3} {n x y : V3} (hD : Dᵀ = D)
    (hv : VanishesOn D n) (hx : dotProduct x n = 0) (hy : dotProduct y n = 0) :
    dotProduct x (D *ᵥ y) = 0 := by
  have hxy : dotProduct (x + y) n = 0 := by
    simp [add_dotProduct, hx, hy]
  have hsum := hv (x + y) hxy
  have hxx := hv x hx
  have hyy := hv y hy
  simp only [mulVec_add, add_dotProduct, dotProduct_add, hxx, hyy] at hsum
  have hswap : dotProduct y (D *ᵥ x) = dotProduct x (D *ᵥ y) := by
    calc
      dotProduct y (D *ᵥ x) = dotProduct (y ᵥ* D) x := dotProduct_mulVec y D x
      _ = dotProduct (y ᵥ* Dᵀ) x := by rw [hD]
      _ = dotProduct (D *ᵥ y) x := by rw [vecMul_transpose]
      _ = dotProduct x (D *ᵥ y) := by rw [dotProduct_comm]
  linarith

lemma mem_span_of_perp {r₁ r₂ x : V3} (hr : Orthonorm r₁ r₂)
    (hx : dotProduct x (r₁ ⨯₃ r₂) = 0) :
    x = dotProduct x r₁ • r₁ + dotProduct x r₂ • r₂ := by
  set a := dotProduct x r₁
  set b := dotProduct x r₂
  set y := x - a • r₁ - b • r₂ with hy
  have hy1 : dotProduct r₁ y = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, hr.dot_first_second,
      hr.norm_first, mul_one, smul_eq_mul, mul_zero, sub_zero]
    ring
  have hy2 : dotProduct r₂ y = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_comm, sub_dotProduct,
      smul_dotProduct, smul_eq_mul, hr.dot_first_second,
      hr.norm_second, smul_eq_mul, mul_zero, sub_zero]
    ring
  have hy0 : dotProduct (r₁ ⨯₃ r₂) y = 0 := by
    simp only [hy, dotProduct_comm, sub_dotProduct, hx, smul_dotProduct, dot_self_cross,
     smul_eq_mul, mul_zero, sub_self, dot_cross_self]
  have hn1 : (r₁ ⨯₃ r₂) ⬝ᵥ (r₁ ⨯₃ r₂) = 1 := by
    rw [cross_dot_cross, hr.dot_first_second, hr.norm_first, hr.norm_second]
    ring
  have hc0 : r₁ ⨯₃ r₂ ⨯₃ y = 0 := by
    rw [cross_cross_eq_smul_sub_smul, hy1, hy2, zero_smul, zero_smul]
    ring
  have hyy : dotProduct y y = 0 := by
    have hC := cross_dot_cross (r₁ ⨯₃ r₂) y (r₁ ⨯₃ r₂) y
    rw [hc0, hn1, hy0] at hC
    rw [zero_dotProduct, one_mul, zero_mul, sub_zero] at hC
    exact hC.symm
  have hy0 : y = 0 := dotProduct_star_self_eq_zero.mp hyy
  rw [hy, sub_sub, sub_eq_zero] at hy0
  exact hy0

lemma dot_swap_of_symm {E : M3} (x y : V3) (hE : Eᵀ = E) :
   dotProduct x (E *ᵥ y) = dotProduct y (E *ᵥ x) := by
  exact IsSymm.dotProduct_mulVec_comm hE

lemma form_on_span {E : M3} {r₁ r₂ x : V3} (hr : Orthonorm r₁ r₂) (hE : Eᵀ = E)
    (c12 : dotProduct r₁ (E *ᵥ r₂) = 0)
    (c11 : dotProduct r₁ (E *ᵥ r₁) = dotProduct r₂ (E *ᵥ r₂))
    (hx : x = dotProduct x r₁ • r₁ + dotProduct x r₂ • r₂) :
    dotProduct x ((E - dotProduct r₁ (E *ᵥ r₁) • 1) *ᵥ x) = 0 := by
  set a := dotProduct x r₁
  set b := dotProduct x r₂
  set μ := dotProduct r₁ (E *ᵥ r₁) with hμ
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
   dotProduct_mulVec, dotProduct_smul, smul_eq_mul]
  have hxx : dotProduct x x = a^2 + b^2 := by
    simp only [hx, dotProduct_add, dotProduct_smul,
      hr.norm_second, hr.dot_first_second, hr.norm_first, dotProduct_comm,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hxE : dotProduct x (E *ᵥ x) = a^2 * μ + b^2 * μ := by
    rw [hx, hμ]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [←c11, dot_swap_of_symm r₂ r₁ hE, c12]
    simp only [mul_zero, add_zero, zero_add]
    ring
  rw [←dotProduct_mulVec, (dot_swap_of_symm x x hE).symm, hxE, hxx]
  ring

lemma mu_eq {D : M3} {n₁ n₂ : V3} {μ₁ μ₂ : ℝ} (h₁₂ : n₁ ⨯₃ n₂ ≠ 0)
    (v₁ : VanishesOn (D - μ₁ • 1) n₁) (v₂ : VanishesOn (D - μ₂ • 1) n₂) :
    μ₁ = μ₂ := by
  set w := n₁ ⨯₃ n₂ with hw
  have hP1 : dotProduct w n₁ = 0 := by
    rw [dotProduct_comm]
    exact dot_self_cross n₁ n₂
  have hP2 : dotProduct w n₂ = 0 := by
    rw [dotProduct_comm]
    exact dot_cross_self n₁ n₂
  specialize v₁ _ hP1
  specialize v₂ _ hP2
  simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_mulVec, dotProduct_smul, smul_eq_mul] at v₁ v₂
  have hwwn0 : dotProduct w w ≠ 0 := by simp [ne_eq, dotProduct_self_eq_zero, h₁₂]
  have e1 : (μ₁ - μ₂) * (dotProduct w w) = 0 := by linarith
  have e2 : μ₁ - μ₂ = 0 := by exact (mul_eq_zero_iff_right hwwn0).mp e1
  linarith


theorem eq_zero_of_vanishesOn_three {D : M3} {n₁ n₂ n₃ : V3} (hD : Dᵀ = D)
    (h₁₂ : n₁ ⨯₃ n₂ ≠ 0) (h₁₃ : n₁ ⨯₃ n₃ ≠ 0) (h₂₃ : n₂ ⨯₃ n₃ ≠ 0)
    (v₁ : VanishesOn D n₁) (v₂ : VanishesOn D n₂) (v₃ : VanishesOn D n₃) :
    D = 0 := by
  sorry
