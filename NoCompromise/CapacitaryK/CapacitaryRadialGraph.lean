module

public import NoCompromise.CapacitaryK.LevelRadialGraph
public import NoCompromise.CapacitaryK.TranslatedDerivatives
public import NoCompromise.CapacitaryK.FarMassDensity

@[expose] public section

/-!
# Capacitary level sets as radial graphs

Chapter 31, `lem:K-level-asymptotics`, `eq:K-rt`, after translation by the
normalized dipole center.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop.CapacitaryK

/-- The Coulomb term has its usual gradient away from the origin. -/
theorem capacitary_gradient_const_div_norm (C : ℝ) {x : E3} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : E3 => C / ‖y‖) x ∧
      gradient (fun y : E3 => C / ‖y‖) x = -(C / ‖x‖ ^ 3) • x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : HasFDerivAt (fun y : E3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    have he : 1 / (2 * ‖x‖) + 1 / (2 * ‖x‖) = ‖x‖⁻¹ := by field_simp; ring
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, two_smul, smul_add, ← add_smul, he] using
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn))
  have hc := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul C
  have hf : HasFDerivAt (fun y : E3 => C / ‖y‖)
      (-(C / ‖x‖ ^ 3) • innerSL ℝ x) x := by
    have he : C * (-(‖x‖ ^ 2)⁻¹ * ‖x‖⁻¹) = -(C / ‖x‖ ^ 3) := by
      field_simp
    simpa only [Function.comp_def, div_eq_mul_inv, smul_smul, he] using hc
  refine ⟨hf.differentiableAt, ?_⟩
  rw [gradient, hf.fderiv, map_smul]
  congr 1
  exact (toDual ℝ E3).symm_apply_apply x

/-- A smooth quadratic homogeneous coefficient gives a derivative of order minus four. -/
theorem capacitary_quadratic_div_norm_fderiv_bound {q : E3 → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : ∀ (c : ℝ) (y : E3), q (c • y) = c ^ 2 * q y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E3, x ≠ 0 →
      DifferentiableAt ℝ (fun y => q y / ‖y‖ ^ 5) x ∧
      ‖fderiv ℝ (fun y => q y / ‖y‖ ^ 5) x‖ ≤ B / ‖x‖ ^ 4 := by
  let f : E3 → ℝ := fun y => q y / ‖y‖ ^ 5
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f ({0}ᶜ : Set E3) := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact (hq.contDiffAt.div ((contDiffAt_id.norm ℝ hx0).pow 5)
      (pow_ne_zero 5 (norm_ne_zero_iff.mpr hx0))).contDiffWithinAt
  have ho : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  have hdf := hf.continuousOn_fderiv_of_isOpen ho (by simp)
  have hsub : sphere (0 : E3) 1 ⊆ ({0}ᶜ : Set E3) := by
    intro x hx
    simp only [mem_sphere, dist_zero_right] at hx
    simpa using (norm_ne_zero_iff.mp (by rw [hx]; norm_num : ‖x‖ ≠ 0))
  obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : E3) 1).image_of_continuousOn
    (hdf.mono hsub)).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (ho.mem_nhds (by simpa using hx))).differentiableAt (by simp)
  refine ⟨hd, ?_⟩
  have hs (c : ℝ) (hc : 0 < c) : (fun y => f (c • y)) = (c ^ 3)⁻¹ • f := by
    funext y
    simp only [f, hqs, norm_smul, Real.norm_of_nonneg hc.le, mul_pow,
      Pi.smul_apply, smul_eq_mul]
    field_simp
  have hscale (c : ℝ) (hc : 0 < c) (y : E3) :
      c • fderiv ℝ f (c • y) = (c ^ 3)⁻¹ • fderiv ℝ f y := by
    have he := congrArg (fun g : E3 → ℝ => fderiv ℝ g y) (hs c hc)
    simpa only [fderiv_comp_smul, fderiv_const_smul_field, Pi.smul_apply] using he
  have hunit : ‖x‖⁻¹ • x ∈ sphere (0 : E3) 1 := by simp [norm_smul, hx]
  have hbound : ‖fderiv ℝ f (‖x‖⁻¹ • x)‖ ≤ max B 0 :=
    (hB _ (mem_image_of_mem _ hunit)).trans (le_max_left _ _)
  have he := congrArg norm (hscale ‖x‖ hn (‖x‖⁻¹ • x))
  have hcancel : ‖x‖ • (‖x‖⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hcancel, norm_smul, norm_smul, Real.norm_of_nonneg hn.le,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le 3))] at he
  have he' : ‖fderiv ℝ f x‖ = ‖fderiv ℝ f (‖x‖⁻¹ • x)‖ / ‖x‖ ^ 4 := by
    apply (eq_div_iff (pow_ne_zero 4 hn.ne')).mpr
    have he' := congrArg (fun a : ℝ => a * ‖x‖ ^ 3) he
    field_simp at he'
    simpa only [one_div, mul_comm] using he'
  rw [he']
  exact div_le_div_of_nonneg_right hbound (pow_nonneg hn.le 4)

/-- `lem:K-level-asymptotics`, `eq:K-rt`: the small capacitary levels are unique
radial graphs about the normalized dipole center, with a uniform quadratic error. -/
theorem capacitary_level_radial_graph
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ Metric.closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball 0 r) ∧
      EqOn v (kelvinTransform u) (Metric.ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ θ : E3, ‖θ‖ = 1 →
        ∃ s : ℝ, 0 < s ∧ u (s • θ + (v 0)⁻¹ • gradient v 0) = t ∧
          |s - (v 0 / t + t * kelvinTranslatedQuadrupole v θ / (v 0) ^ 2)| ≤ A * t ^ 2 ∧
          ∀ s' : ℝ, 0 < s' → u (s' • θ + (v 0)⁻¹ • gradient v 0) = t → s' = s := by
  obtain ⟨v, r, hr, hv, he, _, hv0, hQc, hQs, _, _, R, M, hR, hW, hbound⟩ :=
    capacitary_translated_remainder_derivatives hK hR₀ hKR hzero hu hh hb hinf
  refine ⟨v, r, hr, hv, he, hv0, ?_⟩
  obtain ⟨B, _, hB⟩ := capacitary_quadratic_div_norm_fderiv_bound
    (translated_quadrupole_contDiff v) hQs
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  let W := kelvinTranslatedRemainder u v
  let f : E3 → ℝ := fun y => kelvinTranslatedQuadrupole v y / ‖y‖ ^ 5
  have hUeq : U = fun y => (W y + v 0 / ‖y‖) + f y := by
    funext y
    dsimp [U, W, f, kelvinTranslatedRemainder]
    ring
  have hgrad : ∀ x : E3, max (R + 1) 1 ≤ ‖x‖ →
      DifferentiableAt ℝ U x ∧
        ‖gradient U x + (v 0 / ‖x‖ ^ 3) • x‖ ≤ (|M| + B) / ‖x‖ ^ 4 := by
    intro x hx
    have hxR : R < ‖x‖ := by have := (le_max_left (R + 1) 1).trans hx; linarith
    have hx1 : 1 ≤ ‖x‖ := (le_max_right (R + 1) 1).trans hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos hx1
    have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
    have hdW : DifferentiableAt ℝ W x :=
      (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hxR)).differentiableAt
        (by simp)
    obtain ⟨hdC, hgC⟩ := capacitary_gradient_const_div_norm (v 0) hx0
    obtain ⟨hdf, hbf⟩ := hB x hx0
    have hdU : DifferentiableAt ℝ U x := by
      rw [hUeq]
      exact (hdW.add hdC).add hdf
    refine ⟨hdU, ?_⟩
    have hg : gradient U x + (v 0 / ‖x‖ ^ 3) • x = gradient W x + gradient f x := by
      have hfd : fderiv ℝ U x = fderiv ℝ W x +
          fderiv ℝ (fun y : E3 => v 0 / ‖y‖) x + fderiv ℝ f x := by
        rw [hUeq]
        exact ((hdW.hasFDerivAt.add hdC.hasFDerivAt).add hdf.hasFDerivAt).fderiv
      rw [gradient, hfd, map_add, map_add]
      change (gradient W x + gradient (fun y : E3 => v 0 / ‖y‖) x + gradient f x) +
        (v 0 / ‖x‖ ^ 3) • x = _
      rw [hgC]
      module
    have hgW : ‖gradient W x‖ = ‖fderiv ℝ W x‖ := (toDual ℝ E3).symm.norm_map _
    have hgf : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := (toDual ℝ E3).symm.norm_map _
    have hpow : ‖x‖ ^ 4 ≤ ‖x‖ ^ 5 := by
      nlinarith [mul_nonneg (pow_nonneg (norm_nonneg x) 4) (sub_nonneg.mpr hx1)]
    have hWM : ‖gradient W x‖ ≤ |M| / ‖x‖ ^ 4 := by
      rw [hgW]
      calc
        ‖fderiv ℝ W x‖ ≤ M / ‖x‖ ^ 5 := (hbound x hxR.le).2.1
        _ ≤ |M| / ‖x‖ ^ 5 := div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
        _ ≤ |M| / ‖x‖ ^ 4 := div_le_div_of_nonneg_left (abs_nonneg M) (by positivity) hpow
    rw [hg]
    calc
      ‖gradient W x + gradient f x‖ ≤ ‖gradient W x‖ + ‖gradient f x‖ := norm_add_le _ _
      _ ≤ |M| / ‖x‖ ^ 4 + B / ‖x‖ ^ 4 := add_le_add hWM (by rw [hgf]; exact hbf)
      _ = (|M| + B) / ‖x‖ ^ 4 := (add_div _ _ _).symm
  exact level_radial_graph (hu.comp (continuous_id.add continuous_const))
    (fun y => capacitary_pos_everywhere hK hzero hu hh hb hinf _) hQc hQs hv0
    (lt_of_lt_of_le one_pos (le_max_right _ _))
    (fun y hy => (hbound y (by have := (le_max_left (R + 1) 1).trans hy; linarith)).1)
    hgrad

end LiquidDrop.CapacitaryK
