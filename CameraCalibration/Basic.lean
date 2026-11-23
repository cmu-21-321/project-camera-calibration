/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Basic

This file contains the basics and definitions of the key structures that are
needed to define this camera calibration problem, starting with most importantly
the `Camera` itself. This also includes key lemmas regarding the matrix representation
of the camera itself (as the inverse `U`). This also defines the notion of normality
to the camera plane with a corresponding homography along with the necessary assumptions
about homographies themselves.

## Main definitions

* `CameraCalibration.Camera`: camera data structure with values representing its inverse
* `CameraCalibration.ConsistentHomographyPair`: defines what it means for a homography to be
consistent with a camera
* `CameraCalibration.Satisfies`: defines conditions that a solution matrix
`B` must satisfy for a homography

## References

* “A Flexible New Technique for Camera Calibration” (2000)

-/

@[expose] public section

open Matrix

notation "M3" => Matrix (Fin 3) (Fin 3) ℝ
notation "V3" => Fin 3 → ℝ

namespace CameraCalibration

/-- The representation of a camera using its inverse as an upper triangular
matrix with positive first 2 diagonal entries. -/
structure Camera where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  ha : 0 < a
  hd : 0 < d

/-- Direct translation of `Camera` into its inverse matrix form. -/
def Camera.U (K : Camera) : M3 :=
  !![K.a, K.b, K.c;
     0, K.d, K.e;
     0, 0, 1]

lemma Camera.det_U (K : Camera) : K.U.det = K.a * K.d := by
  simp [Camera.U, Matrix.det_fin_three]

lemma Camera.isUnit_det_U (K : Camera) : IsUnit K.U.det := by
  rw [K.det_U]
  exact (mul_pos K.ha K.hd).ne'.isUnit

lemma Camera.inv_mul_U (K : Camera) : K.U⁻¹ * K.U = 1 :=
  Matrix.nonsing_inv_mul (A := K.U) K.isUnit_det_U

lemma Camera.U_mul_inv (K : Camera) : K.U * K.U⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (A := K.U) K.isUnit_det_U

lemma Camera.eq_conj (K : Camera) (B : M3) : B = K.Uᵀ * ((K.U⁻¹)ᵀ * B * K.U⁻¹) * K.U := by
  calc
    B = 1 * B * (K.U⁻¹ * K.U) := by rw [K.inv_mul_U, mul_one, one_mul]
    _ = 1ᵀ * B * (K.U⁻¹ * K.U) := by rw [transpose_one]
    _ = (K.U⁻¹ * K.U)ᵀ * B * (K.U⁻¹ * K.U) := by rw [K.inv_mul_U]
    _ = K.Uᵀ * (K.U⁻¹)ᵀ * B * (K.U⁻¹ * K.U) := by rw [transpose_mul]
    _ = K.Uᵀ * ((K.U⁻¹)ᵀ * B * K.U⁻¹) * K.U := by simp only [mul_assoc]

/-- Get the normal of the plane determined by the camera inverse intrinsic and the homography. -/
def Camera.normal (K : Camera) (H : M3) : V3 :=
  (K.U *ᵥ Hᵀ 0) ⨯₃ (K.U *ᵥ Hᵀ 1)

lemma Camera.normal_eq {K : Camera} {H : M3} {s : ℝ} {r₁ r₂ : V3}
    (h1 : K.U *ᵥ Hᵀ 0 = s • r₁) (h2 : K.U *ᵥ Hᵀ 1 = s • r₂) :
    K.normal H = (s * s) • (r₁ ⨯₃ r₂) := by
  simp [Camera.normal, h1, h2, smul_smul]

/-- Key definition which says that a homography and camera pair preserves the following properties:
s ≠ 0, r₁ and r₂ are orthonormal, and U times columns 0 and 1 of H equals s • r₁ and s • r₂.
This comes definitionally with the construction of homography matrices in this field. -/
@[mk_iff]
structure ConsistentHomographyPair (K : Camera) (H : M3) (s : ℝ) (r₁ r₂ : V3) : Prop where
  ne_zero : s ≠ 0
  orthonormal : Orthonormal ℝ ![WithLp.toLp 2 r₁, WithLp.toLp 2 r₂]
  mulVec_col_zero : K.U *ᵥ Hᵀ 0 = s • r₁
  mulVec_col_one : K.U *ᵥ Hᵀ 1 = s • r₂

lemma dotProduct_eq_of_orthonormal {r₁ r₂ : V3}
    (h : Orthonormal ℝ ![WithLp.toLp 2 r₁, WithLp.toLp 2 r₂]) :
    r₁ ⬝ᵥ r₁ = 1 ∧ r₂ ⬝ᵥ r₂ = 1 ∧ r₁ ⬝ᵥ r₂ = 0 := by
  have h' := orthonormal_iff_ite.mp h
  have h00 := h' 0 0
  have h11 := h' 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
  rw [EuclideanSpace.inner_toLp_toLp] at h00 h11
  refine ⟨by simpa using h00, by simpa using h11, ?_⟩
  simpa [EuclideanSpace.inner_toLp_toLp] using h' 1 0

/-- Our condition for a solution `B` to preserve necessary constraints for given `H`.
(1) h₁ᵀBh₂ = 0
(2) h₁ᵀBh₁ = h₂ᵀBh₂
as laid out by Zhang -/
def Satisfies (B : M3) (H : M3) : Prop :=
  Hᵀ 0 ⬝ᵥ (B *ᵥ Hᵀ 1) = 0 ∧
    Hᵀ 0 ⬝ᵥ (B *ᵥ Hᵀ 0) = Hᵀ 1 ⬝ᵥ (B *ᵥ Hᵀ 1)

end CameraCalibration
