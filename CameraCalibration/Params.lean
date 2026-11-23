/-
Copyright (c) 2026 Roman Reddick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roman Reddick
-/
module

public import Mathlib.Algebra.Order.Star.Real

/-!
# Params

Key theorem that uses an implicit matrix equality passed in by `Recovery.lean`
 when it uses this theorem to prove that all entries of the two matrices are equal
 and thus so are the matrices. Given that these are defined by the params of a camera
this proves that the params are unique given arbitrary camera inputs.

## Main results

* `CameraCalibration.params_unique`: Takes in the structure of an implicit
camera product `K'.Uᵀ * K'.U = c • (K.Uᵀ * K.U)` via many passed in equalities
representing corresponding matrix entries and uses it to prove that all the entries are equal.
-/

public section

namespace CameraCalibration

theorem params_unique {a b c d e a' b' c' d' e' s : ℝ}
    (ha : 0 < a) (hd : 0 < d) (ha' : 0 < a') (hd' : 0 < d')
    (h00 : a' ^ 2 = s • a ^ 2)
    (h01 : a' * b' = s • (a * b))
    (h02 : a' * c' = s • (a * c))
    (h11 : b' ^ 2 + d' ^ 2 = s • (b ^ 2 + d ^ 2))
    (h12 : b' * c' + d' * e' = s • (b * c + d * e))
    (h22 : c' ^ 2 + e' ^ 2 + 1 = s • (c ^ 2 + e ^ 2 + 1)) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d ∧ e' = e := by
  simp only [smul_eq_mul] at h00 h01 h02 h11 h12 h22
  have hs : 0 < s := by
    have : 0 ≤ s * a ^ 2 := by
      rw [← h00]
      positivity
    nlinarith
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ s = t ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, (Real.sq_sqrt hs.le).symm⟩
  have h00_eq : a' = t * a := by
    have sq_eq : a' ^ 2 = (t * a) ^ 2 := by linarith
    exact (sq_eq_sq₀ (by linarith) (by positivity)).mp sq_eq
  subst a'
  have h01_eq : b' = t * b := by
    have : (a * t) * b' = (a * t) * (t * b) := by linarith
    exact mul_left_cancel₀ (by positivity) this
  subst b'
  have h02_eq : c' = t * c := by
    have : (a * t) * c' = (a * t) * (t * c) := by linarith
    exact mul_left_cancel₀ (by positivity) this
  subst c'
  have h11_eq : d' = t * d := by
    have : (t * b) ^ 2 + d' ^ 2 = (t * b) ^ 2 + (t * d) ^ 2 := by linarith
    have sq_eq := add_left_cancel this
    exact (sq_eq_sq₀ (by linarith) (by positivity)).mp sq_eq
  subst d'
  have h12_eq : e' = t * e := by
    have : (t ^ 2 * b * c) + (t * d) * e' = (t ^ 2 * b * c) + (t * d) * (t * e) := by linarith
    have add_eq : (t * d) * e' = (t * d) * (t * e) := add_left_cancel this
    exact mul_left_cancel₀ (by positivity) add_eq
  subst e'
  have htOne : t = 1 := by
    have : t ^ 2 * c ^ 2 + t ^ 2 * e ^ 2 + t ^ 2 = t ^ 2 * c ^ 2 + t ^ 2 * e ^ 2 + 1 := by
      linarith
    exact (pow_eq_one_iff_of_nonneg ht.le two_ne_zero).mp (add_left_cancel this)
  subst t
  simp

end CameraCalibration
