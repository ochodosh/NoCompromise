module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-!
# Hölder comparison of limiting normals from two-centre estimates

Blueprint `thm:eps-regularity`, Step 4, the arithmetic of the dyadic choice.
Two sequences of axes, selected at two centres at the common scales
`θ ^ j * s₀`, both converge at the geometric rate `θ ^ (j / 2)`, and at every
scale containing both centres (`d ≤ θ ^ j * s₀ / 4`) their squared distance is
controlled by the two excesses, which decay like `θ ^ j`. Choosing the smallest
such scale gives the `1/2`-Hölder bound for the two limits. The statement is
abstract: the excess values and the comparison hypothesis are inputs.
-/

noncomputable section
open Filter
open scoped Topology
namespace LiquidDrop

private lemma rpow_half_eq_sqrt_pow {θ : ℝ} (hθ : 0 ≤ θ) (j : ℕ) :
    θ ^ ((j : ℝ) / 2) = Real.sqrt (θ ^ j) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hθ]
  ring_nf

/-- At every scale containing both centres, the two limits differ by at most
`(2 C + √(2 K C)) θ ^ (j / 2) √T`. -/
lemma limit_dist_le_of_scale {X : Type*} [NormedAddCommGroup X]
    {θ C K T d s₀ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    {νx νy : ℕ → X} {ℓx ℓy : X} {ex ey : ℕ → ℝ}
    (hex : ∀ j, ex j ≤ C * θ ^ j * T) (hey : ∀ j, ey j ≤ C * θ ^ j * T)
    (hxr : ∀ j, ‖νx j - ℓx‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T)
    (hyr : ∀ j, ‖νy j - ℓy‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T)
    (hcomp : ∀ j : ℕ, d ≤ θ ^ j * s₀ / 4 → ‖νx j - νy j‖ ^ 2 ≤ K * (ex j + ey j))
    {j : ℕ} (hj : d ≤ θ ^ j * s₀ / 4) :
    ‖ℓx - ℓy‖ ≤ (2 * C + Real.sqrt (2 * K * C)) * θ ^ ((j : ℝ) / 2) * Real.sqrt T := by
  have hθj : 0 ≤ θ ^ j := pow_nonneg hθ.le j
  have hmid : ‖νx j - νy j‖ ≤ Real.sqrt (2 * K * C) * θ ^ ((j : ℝ) / 2) * Real.sqrt T := by
    have h1 : ‖νx j - νy j‖ ^ 2 ≤ 2 * K * C * θ ^ j * T := by
      have := hcomp j hj
      nlinarith [hex j, hey j]
    have h2 : ‖νx j - νy j‖ ≤ Real.sqrt (2 * K * C * θ ^ j * T) :=
      Real.le_sqrt_of_sq_le h1
    have h3 : Real.sqrt (2 * K * C * θ ^ j * T) =
        Real.sqrt (2 * K * C) * Real.sqrt (θ ^ j) * Real.sqrt T := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [rpow_half_eq_sqrt_pow hθ.le]
    linarith
  have htri : ‖ℓx - ℓy‖ ≤ ‖νx j - ℓx‖ + ‖νx j - νy j‖ + ‖νy j - ℓy‖ := by
    have he : ℓx - ℓy = -(νx j - ℓx) + (νx j - νy j) + (νy j - ℓy) := by abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
    rw [norm_neg]
  have := hxr j
  have := hyr j
  nlinarith

/-- Blueprint `thm:eps-regularity`, Step 4, dyadic arithmetic: the two limits
satisfy the `1/2`-Hölder bound in the distance `d` of the centres, relative to
the initial scale `s₀`, with a constant depending only on `θ`, `C`, and `K`. -/
theorem limit_holder_of_two_centre {X : Type*} [NormedAddCommGroup X]
    {θ C K T d s₀ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hd : 0 ≤ d) (hs₀ : 0 < s₀)
    {νx νy : ℕ → X} {ℓx ℓy : X} {ex ey : ℕ → ℝ}
    (hex : ∀ j, ex j ≤ C * θ ^ j * T) (hey : ∀ j, ey j ≤ C * θ ^ j * T)
    (hxr : ∀ j, ‖νx j - ℓx‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T)
    (hyr : ∀ j, ‖νy j - ℓy‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt T)
    (h0 : νx 0 = νy 0)
    (hcomp : ∀ j : ℕ, d ≤ θ ^ j * s₀ / 4 → ‖νx j - νy j‖ ^ 2 ≤ K * (ex j + ey j)) :
    ‖ℓx - ℓy‖ ≤ (2 * C + Real.sqrt (2 * K * C)) * (2 / Real.sqrt θ) *
      Real.sqrt (d / s₀) * Real.sqrt T := by
  set A := 2 * C + Real.sqrt (2 * K * C) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have hsT := Real.sqrt_nonneg T
  have hsd := Real.sqrt_nonneg (d / s₀)
  have hscale := fun j (hj : d ≤ θ ^ j * s₀ / 4) =>
    limit_dist_le_of_scale hθ hC hK hex hey hxr hyr hcomp hj
  by_cases hfar : θ ^ 0 * s₀ / 4 < d
  · -- far case: compare both limits with the common initial axis
    have hx0 := hxr 0
    have hy0 := hyr 0
    simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one] at hx0 hy0
    have htri : ‖ℓx - ℓy‖ ≤ ‖νx 0 - ℓx‖ + ‖νy 0 - ℓy‖ := by
      have he : ℓx - ℓy = -(νx 0 - ℓx) + (νy 0 - ℓy) := by rw [h0]; abel
      rw [he]
      exact (norm_add_le _ _).trans (by rw [norm_neg])
    have hds : 1 / 4 < d / s₀ := by
      rw [pow_zero, one_mul] at hfar
      rw [lt_div_iff₀ hs₀]; linarith
    have hsq : 1 / 2 < Real.sqrt (d / s₀) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hds
    have hsθ1 : Real.sqrt θ ≤ 1 := Real.sqrt_le_one.mpr hθ1.le
    have hfac : 1 ≤ (2 / Real.sqrt θ) * Real.sqrt (d / s₀) := by
      have h2 : 2 ≤ 2 / Real.sqrt θ := by
        rw [le_div_iff₀ hsθ]; linarith
      nlinarith
    have hCA : 2 * C ≤ A := by
      simp only [hA]; linarith [Real.sqrt_nonneg (2 * K * C)]
    calc ‖ℓx - ℓy‖ ≤ 2 * C * Real.sqrt T := by linarith
      _ ≤ A * Real.sqrt T := mul_le_mul_of_nonneg_right hCA hsT
      _ = A * 1 * Real.sqrt T := by ring
      _ ≤ A * ((2 / Real.sqrt θ) * Real.sqrt (d / s₀)) * Real.sqrt T := by
          gcongr
      _ = A * (2 / Real.sqrt θ) * Real.sqrt (d / s₀) * Real.sqrt T := by ring
  · replace hfar : d ≤ θ ^ 0 * s₀ / 4 := not_lt.mp hfar
    by_cases hd0 : d = 0
    · -- coincident centres: every scale is admissible, so the limits agree
      have hle : ∀ j : ℕ, ‖ℓx - ℓy‖ ≤ A * θ ^ ((j : ℝ) / 2) * Real.sqrt T := fun j =>
        hscale j (by rw [hd0]; positivity)
      have htend : Tendsto (fun j : ℕ => A * θ ^ ((j : ℝ) / 2) * Real.sqrt T) atTop
          (𝓝 0) := by
        have hs : Tendsto (fun j : ℕ => Real.sqrt (θ ^ j)) atTop (𝓝 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).sqrt
          simpa using this
        simp_rw [rpow_half_eq_sqrt_pow hθ.le]
        simpa using (hs.const_mul A).mul_const (Real.sqrt T)
      have h0' : ‖ℓx - ℓy‖ ≤ 0 := ge_of_tendsto htend (Eventually.of_forall hle)
      have hrhs : 0 ≤ A * (2 / Real.sqrt θ) * Real.sqrt (d / s₀) * Real.sqrt T := by
        positivity
      linarith
    · -- choose the last scale containing both centres
      have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hex_fail : ∃ j : ℕ, ¬ d ≤ θ ^ j * s₀ / 4 := by
        have ht : Tendsto (fun j : ℕ => θ ^ j * s₀ / 4) atTop (𝓝 0) := by
          simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ1).mul_const s₀).div_const
            (4 : ℝ)
        obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hdpos)).exists
        exact ⟨j, not_le.mpr hj⟩
      classical
      let k := Nat.find hex_fail
      have hk : ¬ d ≤ θ ^ k * s₀ / 4 := Nat.find_spec hex_fail
      have hk0 : k ≠ 0 := by
        intro h
        apply hk
        rw [h]
        exact hfar
      obtain ⟨j, hjk⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
      have hj : d ≤ θ ^ j * s₀ / 4 := by
        exact not_not.mp (Nat.find_min hex_fail (show j < k by omega))
      have hk' : θ ^ (j + 1) * s₀ / 4 < d := by rw [← hjk]; exact not_le.mp hk
      have hθj : θ ^ j ≤ 4 * d / (θ * s₀) := by
        rw [le_div_iff₀ (mul_pos hθ hs₀)]
        rw [pow_succ] at hk'
        nlinarith
      have hsqrt : θ ^ ((j : ℝ) / 2) ≤ (2 / Real.sqrt θ) * Real.sqrt (d / s₀) := by
        rw [rpow_half_eq_sqrt_pow hθ.le]
        calc Real.sqrt (θ ^ j) ≤ Real.sqrt (4 * d / (θ * s₀)) := Real.sqrt_le_sqrt hθj
          _ = (2 / Real.sqrt θ) * Real.sqrt (d / s₀) := by
            rw [show 4 * d / (θ * s₀) = 2 ^ 2 * (d / s₀) / θ by field_simp; ring,
              Real.sqrt_div' _ hθ.le, Real.sqrt_mul (by positivity),
              Real.sqrt_sq (by norm_num)]
            ring
      calc ‖ℓx - ℓy‖ ≤ A * θ ^ ((j : ℝ) / 2) * Real.sqrt T := hscale j hj
        _ ≤ A * ((2 / Real.sqrt θ) * Real.sqrt (d / s₀)) * Real.sqrt T := by gcongr
        _ = A * (2 / Real.sqrt θ) * Real.sqrt (d / s₀) * Real.sqrt T := by ring

end LiquidDrop
