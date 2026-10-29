import MathLib

open Matrix

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev V3 := Fin 3 → ℝ

structure Camera where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  ha : 0 < a
  hb : 0 < b

def Camera.U (K : Camera) : M3 :=
  !![K.a, K.b, K.c;
     0, K.d, K.e;
     0, 0, 1]

structure HomographyM3 where
  h₁ : V3
  h₂ : V3
  h₃ : V3
  normalized : h₃ 2 = 1

structure Orthonorm (u v : V3) : Prop where
  norm_first : dotProduct u u = 1
  norm_second : dotProduct v v = 1
  dot_first_second : dotProduct u v = 0

def ConsistentHomographyPair (K : Camera) (H : HomographyM3) : Prop :=
  ∃ (s : ℝ), s ≠ 0 ∧ ∃ r₁ r₂ t : V3,
  (Orthonorm r₁ r₂) ∧
  K.U *ᵥ H.h₁ = s • r₁ ∧
  K.U *ᵥ H.h₂ = s • r₂ ∧
  K.U *ᵥ H.h₃ = s • t

def Satisfies (B : M3) (H : HomographyM3) : Prop :=
  dotProduct H.h₁ (B *ᵥ H.h₂) = 0 ∧
  dotProduct H.h₁ (B *ᵥ H.h₁) = dotProduct H.h₂ (B *ᵥ H.h₂)

def UniqueToScaleFactor (Hs : List HomographyM3) :=
  ∀ B B' : M3, B = Bᵀ → B' = B'ᵀ →
  (∀ H ∈ Hs, Satisfies B H) → (∀ H ∈ Hs, Satisfies B' H)
  → B ≠ 0 → ∃ s : ℝ, B' = s • B
