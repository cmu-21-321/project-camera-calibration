import CameraCalibration.Basic

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
      have : 0 ≤ s * a^2 := by
        rw [←h00]
        positivity
      nlinarith

    have construction : ∃ t, 0 < t ∧ s = t^2 := by
      refine ⟨Real.sqrt s, ?_, ?_⟩
      · exact Real.sqrt_pos.mpr hs
      · have : 0 ≤ s := hs.le
        exact (Real.sq_sqrt this).symm

    obtain ⟨t, ht, hst⟩ := construction
    subst s

    have h00_eq : a' = t * a := by
      have sq_eq : a'^2 = (t * a)^2 := by linarith
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
      have : (t * b)^2 + d'^2 = (t * b)^2 + (t * d)^2 := by linarith
      have sq_eq := add_left_cancel this
      exact (sq_eq_sq₀ (by linarith) (by positivity)).mp sq_eq
    subst d'

    have h12_eq : e' = t * e := by
      have : (t^2 * b * c) + (t * d) * e' = (t^2 * b * c) + (t * d) * (t * e) := by linarith
      have add_eq : (t * d) * e' = (t * d) * (t * e) := add_left_cancel this
      exact mul_left_cancel₀ (by positivity) add_eq
    subst e'

    have htOne : t = 1 := by
      have : t^2 * c^2 + t^2 * e^2 + t^2 = t^2 * c^2 + t^2 * e^2 + 1 := by linarith
      have add_eq := add_left_cancel this
      rcases sq_eq_one_iff.mp add_eq with ht1 | htn1
      · exact ht1
      · linarith
    subst t
    simp
