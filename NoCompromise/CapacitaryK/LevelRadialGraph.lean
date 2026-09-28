import NoCompromise.CapacitaryK.LevelSandwich
import NoCompromise.CapacitaryK.PolarMass

/-!
# `lem:K-level-asymptotics`, `eq:K-rt`: small levels are radial graphs

If `U = C/|y| + q(y)/|y|⁵ + O(|y|⁻⁴)` (continuous, positive) and in addition the gradient satisfies
`∇U = -C y/|y|³ + O(|y|⁻⁴)` on the far region, then for all small `t > 0` every ray from the origin
meets `{U = t}` exactly once, at a radius `r_t(θ)` with
`|r_t(θ) - (C/t + t q(θ)/C²)| ≤ A t²`, uniformly in `θ` (`level_radial_graph`).
-/

noncomputable section
open Real Set Filter Topology Metric
open scoped Gradient

namespace LiquidDrop.CapacitaryK

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Along a ray, the radial derivative is negative in the far field. -/
theorem ray_strictAntiOn {U : E₃ → ℝ} {C R B : ℝ} (hC : 0 < C)
    (hgrad : ∀ x : E₃, R ≤ ‖x‖ →
      DifferentiableAt ℝ U x ∧ ‖gradient U x + (C / ‖x‖ ^ 3) • x‖ ≤ B / ‖x‖ ^ 4)
    {θ : E₃} (hθ : ‖θ‖ = 1) :
    StrictAntiOn (fun s : ℝ => U (s • θ)) (Ici (max R (max 1 (2 * |B| / C)))) := by
  set R' := max R (max 1 (2 * |B| / C)) with hR'
  have hR1 : 1 ≤ R' := (le_max_left _ _).trans (le_max_right _ _)
  have hRR : R ≤ R' := le_max_left _ _
  have hRB : 2 * |B| / C ≤ R' := (le_max_right _ _).trans (le_max_right _ _)
  have hnorm : ∀ s : ℝ, 0 < s → ‖s • θ‖ = s := by
    intro s hs; rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  have hderiv : ∀ s : ℝ, R' ≤ s →
      HasDerivAt (fun s : ℝ => U (s • θ)) (inner ℝ (gradient U (s • θ)) θ) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos (hR1.trans hs)
    have hd := (hgrad (s • θ) (by rw [hnorm s hs0]; exact hRR.trans hs)).1
    have h1 : HasDerivAt (fun s : ℝ => s • θ) θ s := by
      simpa using (hasDerivAt_id s).smul_const θ
    have h2 := hd.hasFDerivAt.comp_hasDerivAt s h1
    have he : inner ℝ (gradient U (s • θ)) θ = fderiv ℝ U (s • θ) θ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [he]
    exact h2
  have hneg : ∀ s : ℝ, R' ≤ s → inner ℝ (gradient U (s • θ)) θ < 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le one_pos (hR1.trans hs)
    have hb := (hgrad (s • θ) (by rw [hnorm s hs0]; exact hRR.trans hs)).2
    rw [hnorm s hs0] at hb
    have hsplit : inner ℝ (gradient U (s • θ)) θ =
        inner ℝ (gradient U (s • θ) + (C / s ^ 3) • (s • θ)) θ - C / s ^ 2 := by
      rw [inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, hθ]
      simp only [conj_trivial]
      field_simp
      ring
    have hcs := real_inner_le_norm (gradient U (s • θ) + (C / s ^ 3) • (s • θ)) θ
    rw [hθ, mul_one] at hcs
    rw [hsplit]
    have hs4 : 0 < s ^ 4 := by positivity
    have hkey : B / s ^ 4 < C / s ^ 2 := by
      rw [div_lt_div_iff₀ hs4 (by positivity)]
      have h2B : 2 * |B| ≤ C * s := by
        have := (div_le_iff₀ hC).mp (hRB.trans hs)
        linarith
      have hs1 : 1 ≤ s := hR1.trans hs
      have hBle : B ≤ |B| := le_abs_self B
      have h3 : 2 * (|B| * s ^ 2) ≤ C * s ^ 3 := by
        have := mul_le_mul_of_nonneg_right h2B (sq_nonneg s)
        nlinarith
      have h4 : s ^ 3 ≤ s ^ 4 := by
        have : 0 ≤ s ^ 3 * (s - 1) := mul_nonneg (by positivity) (by linarith)
        nlinarith
      have h5 : 0 < C * s ^ 3 := by positivity
      have h6 : B * s ^ 2 ≤ |B| * s ^ 2 := mul_le_mul_of_nonneg_right hBle (sq_nonneg s)
      have h7 : C * s ^ 3 ≤ C * s ^ 4 := mul_le_mul_of_nonneg_left h4 hC.le
      nlinarith
    linarith
  have hcont : ContinuousOn (fun s : ℝ => U (s • θ)) (Ici R') := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  apply strictAntiOn_of_deriv_neg (convex_Ici R') hcont
  intro s hs
  rw [interior_Ici] at hs
  rw [(hderiv s (le_of_lt hs)).deriv]
  exact hneg s (le_of_lt hs)

/-- `eq:K-rt` as a radial graph: for small `t`, each ray meets `{U = t}` exactly once, at
`r_t(θ) = C/t + t q(θ)/C² + O(t²)` uniformly in `θ`. -/
theorem level_radial_graph {U q : E₃ → ℝ} (hUc : Continuous U) (hUpos : ∀ y, 0 < U y)
    (hqc : Continuous q) (hqh : ∀ (c : ℝ) (y : E₃), q (c • y) = c ^ 2 * q y)
    {C R M B : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hU : ∀ y : E₃, R ≤ ‖y‖ → |U y - C / ‖y‖ - q y / ‖y‖ ^ 5| ≤ M / ‖y‖ ^ 4)
    (hgrad : ∀ x : E₃, R ≤ ‖x‖ →
      DifferentiableAt ℝ U x ∧ ‖gradient U x + (C / ‖x‖ ^ 3) • x‖ ≤ B / ‖x‖ ^ 4) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ θ : E₃, ‖θ‖ = 1 →
      ∃ s : ℝ, 0 < s ∧ U (s • θ) = t ∧ |s - (C / t + t * q θ / C ^ 2)| ≤ A * t ^ 2 ∧
        ∀ s' : ℝ, 0 < s' → U (s' • θ) = t → s' = s := by
  obtain ⟨A₀, hA₀⟩ := level_sandwich hUc hUpos hqc hqh hC hR hU
  set A := |A₀| with hAdef
  refine ⟨A, abs_nonneg _, ?_⟩
  obtain ⟨Bq, hBq0, hBq⟩ := polar_homogeneous_bound hqc hqh
  set R' := max R (max 1 (2 * |B| / C)) with hR'
  have hR'1 : 1 ≤ R' := (le_max_left _ _).trans (le_max_right _ _)
  set D : ℝ := 2 * R' + Bq / C ^ 2 + A with hD
  have hDpos : 0 < D := by
    have : 0 ≤ Bq / C ^ 2 := div_nonneg hBq0 (sq_nonneg _)
    have := abs_nonneg A₀
    linarith
  filter_upwards [hA₀, Ioo_mem_nhdsGT (lt_min one_pos (div_pos hC hDpos))] with t hAt ht
  intro θ hθ
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.le.trans (min_le_left _ _)
  have htD : t ≤ C / D := ht.2.le.trans (min_le_right _ _)
  have hCt : D ≤ C / t := by
    rw [le_div_iff₀ ht0]; rw [le_div_iff₀ hDpos] at htD; linarith
  have hθ0 : θ ≠ 0 := by intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
  have hqθ : |q θ| ≤ Bq := by simpa [hθ] using hBq θ hθ0
  have hnorm : ∀ s : ℝ, 0 < s → ‖s • θ‖ = s := by
    intro s hs; rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  have hray : ∀ s : ℝ, 0 < s → t * q (s • θ) / (C ^ 2 * ‖s • θ‖ ^ 2) = t * q θ / C ^ 2 := by
    intro s hs
    rw [hnorm s hs, hqh]
    field_simp
  set ρ := C / t + t * q θ / C ^ 2 with hρ
  have htq : t * q θ / C ^ 2 ≥ -(Bq / C ^ 2) := by
    have h1 := (abs_le.mp hqθ).1
    have h2 : -Bq ≤ t * q θ := by
      nlinarith [mul_le_mul_of_nonneg_left h1 ht0.le, mul_le_mul_of_nonneg_right ht1 hBq0]
    have h3 : -Bq / C ^ 2 ≤ t * q θ / C ^ 2 := div_le_div_of_nonneg_right h2 (sq_nonneg _)
    rw [neg_div] at h3
    linarith
  have hAt2 : A * t ^ 2 ≤ A := by
    have : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [abs_nonneg A₀]
  have hAt2' : 0 ≤ A * t ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hA0le : A₀ * t ^ 2 ≤ A * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  -- the lower radius is at least `2 R'`
  have hlow : 2 * R' ≤ ρ - A * t ^ 2 := by linarith
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos hR'1
  have hanti := ray_strictAntiOn hC hgrad hθ
  -- endpoints for the intermediate value theorem
  set sp := ρ + A * t ^ 2 with hsp
  set sm := (ρ - A * t ^ 2) / 2 with hsm
  have hsmpos : 0 < sm := by rw [hsm]; linarith
  have hsmsp : sm ≤ sp := by rw [hsm, hsp]; linarith
  have hsppos : 0 < sp := lt_of_lt_of_le hsmpos hsmsp
  have hfp : U (sp • θ) ≤ t := by
    apply hAt.1 _ (smul_ne_zero hsppos.ne' hθ0)
    rw [hray sp hsppos, hnorm sp hsppos, hsp]
    linarith
  have hfm : t < U (sm • θ) := by
    by_contra hcon
    push Not at hcon
    have := (hAt.2 _ hcon).2
    rw [hray sm hsmpos, hnorm sm hsmpos] at this
    rw [hsm] at this
    linarith
  have hcont : ContinuousOn (fun s : ℝ => U (s • θ)) (Icc sm sp) :=
    (hUc.comp (continuous_id.smul continuous_const)).continuousOn
  obtain ⟨s, hsI, hs⟩ := intermediate_value_Icc' hsmsp hcont ⟨hfp, hfm.le⟩
  have hs0 : 0 < s := lt_of_lt_of_le hsmpos hsI.1
  have hsol : ∀ s' : ℝ, 0 < s' → U (s' • θ) = t → ρ - A * t ^ 2 ≤ s' := by
    intro s' hs' hU'
    have := (hAt.2 _ hU'.le).2
    rw [hray s' hs', hnorm s' hs'] at this
    linarith
  have hsl := hsol s hs0 hs
  refine ⟨s, hs0, hs, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [hsI.2]
  · intro s' hs' hU'
    have hsl' := hsol s' hs' hU'
    have hmem : ∀ r, ρ - A * t ^ 2 ≤ r → r ∈ Ici R' := fun r hr => by
      simp only [mem_Ici]; linarith
    exact hanti.injOn (hmem s' hsl') (hmem s hsl) (hU'.trans hs.symm)

end LiquidDrop.CapacitaryK
