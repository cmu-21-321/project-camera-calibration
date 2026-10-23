import mathlib

open Matrix

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev V3 := Fin 3 → ℝ

structure IsIntrinsic (K : M3) : Prop where
  α : 0 < K 0 0
  β : 0 < K 1 1
  γ : 0 < K 0 1
  u₀ : 0 < K 0 2
  u₁ : 0 < K 1 2
  zero_1_0 : K 1 0 = 0
  zero_2_0 : K 2 0 = 0
  zero_2_1 : K 2 1 = 0
  one_2_2 : K 2 2 = 1

structure Orthonorm (u v : V3) : Prop where
  self_first : dotProduct u u = 1
  self_second : dotProduct u u = 1
  cross : dotProduct u v = 0

def ConsistentHomographyPair (A H : M3) : Prop :=
  ∃ (λ : ℝ) (r₁ r₂ t : V3), (Orthonorm r₁ r₂) ∧ H = λ * ![r₁ r₂ t]

theorem zhang_three_view_uniqueness (h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair A H) A = A' := by
  sorry
