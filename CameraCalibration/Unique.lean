import CameraCalibration.Basic
import CameraCalibration.Plane

open Matrix

lemma conj_dot (A B : M3) (u v : V3) :
    dotProduct u ((Aᵀ * B * A) *ᵥ v) = dotProduct (A *ᵥ u) (B *ᵥ (A *ᵥ v)) := by
  simp only [←Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

lemma conj_symm {B : M3} {K : Camera} (hB : B = Bᵀ) :
  (K.Aᵀ * B * K.A)ᵀ = K.Aᵀ * B * K.A := by
  simp [hB.symm, transpose_mul, mul_assoc]

-- since Uh_1 = sr_1 we can get h_1 = A(s * r_2)
-- similar for h_2
lemma view_constraints {K : Camera} {H : HomographyM3} {B : M3} {s : ℝ} {r₁ r₂ : V3}
    (hs0 : s ≠ 0)
    (h1 : K.U *ᵥ H.h₁ = s • r₁)
    (h2 : K.U *ᵥ H.h₂ = s • r₂)
    (hs : Satisfies B H) :
    dotProduct r₁ ((K.Aᵀ * B * K.A) *ᵥ r₂) = 0 ∧
    dotProduct r₁ ((K.Aᵀ * B * K.A) *ᵥ r₁) = dotProduct r₂ ((K.Aᵀ * B * K.A) *ᵥ r₂) := by
  obtain ⟨c1, c2⟩ := hs
  have e1 : H.h₁ = s • (K.A *ᵥ r₁) := by
    have := congrArg (fun v => K.A *ᵥ v) h1
    simp only [mulVec_mulVec, K.A_mul_U, one_mulVec, mulVec_smul] at this
    assumption
  have e2 : H.h₂ = s • (K.A *ᵥ r₂) := by
    have := congrArg (fun v => K.A *ᵥ v) h2
    simp only [mulVec_mulVec, K.A_mul_U, one_mulVec, mulVec_smul] at this
    assumption
  simp only [conj_dot]
  constructor
  · rw [e1, e2] at c1
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at c1
    simpa [hs0] using c1
  · rw [e1, e2] at c2
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at c2
    simpa [hs0] using c2

lemma plane_form {K : Camera} {H : HomographyM3} {B : M3} (hB : B = Bᵀ)
    (hc : ConsistentHomographyPair K H) (hs : Satisfies B H) :
    ∃ μ : ℝ, VanishesOn (K.Aᵀ * B * K.A - μ • 1) (K.normal H) := by
  obtain ⟨s, hs0, r₁, r₂, t, hr, h1, h2, _⟩ := hc
  obtain ⟨c11, c12⟩ := view_constraints hs0 h1 h2 hs
  refine ⟨(dotProduct r₁ ((K.Aᵀ * B * K.A) *ᵥ r₁)), ?_⟩
  intro x hx
  rw [K.normal_eq h1 h2, dotProduct_smul, smul_eq_mul] at hx
  have hx' := by simpa [hs0] using hx
  exact form_on_span hr (conj_symm hB) c11 c12 (mem_span_of_perp hr hx')

theorem eq_smul_gram {K : Camera} {H₁ H₂ H₃ : HomographyM3} {B : M3} (hB : B = Bᵀ)
    (h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
    (hs : ∀ H ∈ [H₁, H₂, H₃], Satisfies B H)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0)
    (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    ∃ μ : ℝ, B = μ • (K.Uᵀ * K.U) := by
  obtain ⟨μ₁, v₁⟩ := plane_form hB (h H₁ (by simp)) (hs H₁ (by simp))
  obtain ⟨μ₂, v₂⟩ := plane_form hB (h H₂ (by simp)) (hs H₂ (by simp))
  obtain ⟨μ₃, v₃⟩ := plane_form hB (h H₃ (by simp)) (hs H₃ (by simp))
  have hμ₁μ₂ : μ₁ = μ₂ := mu_eq h₁₂ v₁ v₂
  have hμ₂μ₃ : μ₂ = μ₃ := mu_eq h₂₃ v₂ v₃
  have hμ₁μ₃ : μ₁ = μ₃ := hμ₁μ₂.trans hμ₂μ₃
  subst hμ₂μ₃ hμ₁μ₃
  have hSymm : K.Aᵀ * B * K.A - μ₁ • 1 = (K.Aᵀ * B * K.A - μ₁ • 1)ᵀ := by
    simp [sub_smul_one_symm μ₁ (conj_symm hB)]
  have hE0 : (K.Aᵀ * B * K.A) - μ₁ • 1 = 0 :=
    eq_zero_of_vanishesOn_three hSymm.symm h₁₂ h₁₃ h₂₃ v₁ v₂ v₃
  have hD : (K.Aᵀ * B * K.A) = μ₁ • 1  := sub_eq_zero.mp hE0
  use μ₁
  calc
    B = K.Uᵀ * (K.Aᵀ * B * K.A) * K.U := K.eq_conj B
    _ = μ₁ • (K.Uᵀ * K.U) := by simp [hD]


theorem unique_of_nonparallel {K : Camera} {H₁ H₂ H₃ : HomographyM3}
    (h : ∀ H ∈ [H₁, H₂, H₃], ConsistentHomographyPair K H)
    (h₁₂ : K.normal H₁ ⨯₃ K.normal H₂ ≠ 0)
    (h₁₃ : K.normal H₁ ⨯₃ K.normal H₃ ≠ 0)
    (h₂₃ : K.normal H₂ ⨯₃ K.normal H₃ ≠ 0) :
    UniqueToScaleFactor [H₁, H₂, H₃] := by
  intro B B' hB hB' hH hH' hN
  obtain ⟨μ, hμ⟩ := eq_smul_gram hB h hH h₁₂ h₁₃ h₂₃
  obtain ⟨μ', hμ'⟩ := eq_smul_gram hB' h hH' h₁₂ h₁₃ h₂₃
  rw [hμ, hμ']
  have hμn : μ ≠ 0 := by
    intro h0
    apply hN
    rw [hμ, h0]
    simp
  use (μ' / μ)
  rw [smul_smul]
  field_simp
