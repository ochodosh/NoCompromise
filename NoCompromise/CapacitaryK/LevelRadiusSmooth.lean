module

public import NoCompromise.CapacitaryK.CapacitaryRadialGraph

@[expose] public section

/-!
# Smoothness of the capacitary level radius

Chapter 31, `lem:K-level-asymptotics`, `eq:K-rt`: the radius of a radial level graph,
extended zero-homogeneously, is smooth away from the origin, with the implicit-function
gradient formula.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- The derivative of the norm away from the origin. -/
theorem levelRadius_hasFDerivAt_norm {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have he : 1 / (2 * ‖x‖) + 1 / (2 * ‖x‖) = ‖x‖⁻¹ := by field_simp; ring
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, two_smul, smul_add, ← add_smul, he] using
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn))

/-- A nonzero scalar multiple of the identity of `ℝ` is invertible. -/
theorem levelRadius_isInvertible_smulRight {c : ℝ} (hc : c ≠ 0) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc), ?_⟩
  ext
  simp [ContinuousLinearEquiv.unitsEquivAut_apply]

/-- Zero-homogeneous radial level radii are smooth off the origin, by the implicit
function theorem applied to `(y, s) ↦ U (s • y)`. -/
theorem levelRadius_contDiffOn {U : E3 → ℝ} {O : Set E3} (hO : IsOpen O)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U O) {t : ℝ} {ρ : E3 → ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hpos : ∀ θ : E3, ‖θ‖ = 1 → 0 < ρ θ)
    (huniq : ∀ θ : E3, ‖θ‖ = 1 → ∀ s : ℝ, 0 < s → U (s • θ) = t → s = ρ θ)
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    (hmem : ∀ θ : E3, ‖θ‖ = 1 → ρ θ • θ ∈ O)
    (hder : ∀ θ : E3, ‖θ‖ = 1 → ⟪gradient U (ρ θ • θ), θ⟫ ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) ρ {y | y ≠ 0} := by
  intro y₀ hy₀
  have hy₀ : y₀ ≠ 0 := hy₀
  have hn₀ : 0 < ‖y₀‖ := norm_pos_iff.mpr hy₀
  set θ₀ : E3 := ‖y₀‖⁻¹ • y₀ with hθ₀def
  have hθ₀ : ‖θ₀‖ = 1 := by
    rw [hθ₀def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn₀.ne']
  set s₀ : ℝ := ρ θ₀ / ‖y₀‖ with hs₀def
  have hx : s₀ • y₀ = ρ θ₀ • θ₀ := by
    rw [hs₀def, hθ₀def, smul_smul, div_eq_mul_inv]
  have hs₀ : 0 < s₀ := div_pos (hpos θ₀ hθ₀) hn₀
  let f : E3 × ℝ → ℝ := fun p => U (p.2 • p.1)
  have hUx : ContDiffAt ℝ (⊤ : ℕ∞) U (s₀ • y₀) :=
    hU.contDiffAt (hO.mem_nhds (hx ▸ hmem θ₀ hθ₀))
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × ℝ => p.2 • p.1) :=
    contDiff_snd.smul contDiff_fst
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) f (y₀, s₀) := hUx.comp (y₀, s₀) hsm.contDiffAt
  have hfd : HasFDerivAt f (fderiv ℝ f (y₀, s₀)) (y₀, s₀) :=
    (hf.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun s : ℝ => f (y₀, s))
      (fderiv ℝ f (y₀, s₀) ∘L ContinuousLinearMap.inr ℝ E3 ℝ) s₀ :=
    hfd.comp s₀ (hasFDerivAt_prodMk_right y₀ s₀)
  have h2 : HasDerivAt (fun s : ℝ => f (y₀, s)) (fderiv ℝ U (s₀ • y₀) ((1 : ℝ) • y₀)) s₀ :=
    (hUx.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s₀
      ((hasDerivAt_id s₀).smul_const y₀)
  have hL : fderiv ℝ f (y₀, s₀) ∘L ContinuousLinearMap.inr ℝ E3 ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (fderiv ℝ U (s₀ • y₀) ((1 : ℝ) • y₀)) :=
    h1.unique h2.hasFDerivAt
  have hc : fderiv ℝ U (s₀ • y₀) ((1 : ℝ) • y₀) ≠ 0 := by
    rw [one_smul]
    have hg : fderiv ℝ U (s₀ • y₀) y₀ = ⟪gradient U (s₀ • y₀), y₀⟫ := by
      rw [gradient, toDual_symm_apply]
    have hy : y₀ = ‖y₀‖ • θ₀ := by
      rw [hθ₀def, smul_smul, mul_inv_cancel₀ hn₀.ne', one_smul]
    rw [hg, hx]
    conv_lhs => rw [hy]
    rw [inner_smul_right]
    exact mul_ne_zero hn₀.ne' (hder θ₀ hθ₀)
  have hi : (fderiv ℝ f (y₀, s₀) ∘L ContinuousLinearMap.inr ℝ E3 ℝ).IsInvertible := by
    rw [hL]; exact levelRadius_isInvertible_smulRight hc
  have pn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := hf.implicitFunction pn hi
  have hψ0 : ψ y₀ = s₀ := hf.implicitFunction_apply_self pn hi
  have hψc : ContDiffAt ℝ (⊤ : ℕ∞) ψ y₀ := hf.contDiffAt_implicitFunction pn hi
  have hψe := hf.eventually_apply_implicitFunction pn hi
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y :=
    hψc.continuousAt.eventually (lt_mem_nhds (hψ0 ▸ hs₀))
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have heq : (fun y => ψ y * ‖y‖) =ᶠ[𝓝 y₀] ρ := by
    filter_upwards [hψe, hψpos, hne] with y hye hyp hy0
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hθ : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
    have hft : f (y₀, s₀) = t := by
      change U (s₀ • y₀) = t
      rw [hx]; exact hroot θ₀ hθ₀
    have hrt : U ((ψ y * ‖y‖) • (‖y‖⁻¹ • y)) = t := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hny.ne', mul_one]
      exact hye.trans hft
    rw [hhom y hy0]
    exact huniq _ hθ _ (mul_pos hyp hny) hrt
  exact ((hψc.mul (contDiffAt_norm ℝ hy₀)).congr_of_eventuallyEq heq.symm).contDiffWithinAt

/-- The gradient of a zero-homogeneous level radius at a unit vector, from differentiating
`U (ρ y • (‖y‖⁻¹ • y)) = t`. -/
theorem levelRadius_gradient {U : E3 → ℝ} {t : ℝ} {ρ : E3 → ℝ}
    (hhom : ∀ y : E3, y ≠ 0 → ρ y = ρ (‖y‖⁻¹ • y))
    (hroot : ∀ θ : E3, ‖θ‖ = 1 → U (ρ θ • θ) = t)
    {θ : E3} (hθ : ‖θ‖ = 1) (hρd : DifferentiableAt ℝ ρ θ)
    (hUd : DifferentiableAt ℝ U (ρ θ • θ))
    (hder : ⟪gradient U (ρ θ • θ), θ⟫ ≠ 0) :
    gradient ρ θ = -(ρ θ / ⟪gradient U (ρ θ • θ), θ⟫) •
      (gradient U (ρ θ • θ) - ⟪gradient U (ρ θ • θ), θ⟫ • θ) := by
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
  let q : E3 → ℝ := fun y => ρ y * ‖y‖⁻¹
  have hconst : (fun y => U (q y • y)) =ᶠ[𝓝 θ] fun _ => t := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny.ne']
    change U ((ρ y * ‖y‖⁻¹) • y) = t
    rw [← smul_smul, hhom y hy]
    exact hroot _ hu
  have hinv := (hasDerivAt_inv (norm_ne_zero_iff.mpr hθ0)).comp_hasFDerivAt θ
    (levelRadius_hasFDerivAt_norm hθ0)
  have hq := hρd.hasFDerivAt.mul hinv
  have hsm : HasFDerivAt (fun y => q y • y) (q θ • ContinuousLinearMap.id ℝ E3 +
      (ρ θ • (-(‖θ‖ ^ 2)⁻¹ • ‖θ‖⁻¹ • innerSL ℝ θ) + ‖θ‖⁻¹ • fderiv ℝ ρ θ).smulRight θ) θ :=
    hq.smul (hasFDerivAt_id θ)
  have hqθ : q θ = ρ θ := by simp [q, hθ]
  have hUd' : HasFDerivAt U (fderiv ℝ U (ρ θ • θ)) (q θ • θ) := by
    rw [hqθ]; exact hUd.hasFDerivAt
  have hcomp := HasFDerivAt.comp (f := fun y => q y • y) θ hUd' hsm
  have hzero := hcomp.unique ((hasFDerivAt_const t θ).congr_of_eventuallyEq hconst)
  have hgU : ∀ w : E3, fderiv ℝ U (ρ θ • θ) w = ⟪gradient U (ρ θ • θ), w⟫ := fun w => by
    rw [gradient, toDual_symm_apply]
  set g := gradient U (ρ θ • θ)
  apply ext_inner_right ℝ
  intro e
  have he := congrArg (fun L : E3 →L[ℝ] ℝ => L e) hzero
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, zero_apply, hgU, inner_add_right,
    inner_smul_right, innerSL_apply_apply, smul_eq_mul, hθ] at he
  rw [gradient, toDual_symm_apply, inner_smul_left, inner_sub_left, inner_smul_left]
  simp only [conj_trivial]
  have hθθ : ⟪θ, θ⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  field_simp
  rw [hqθ] at he
  norm_num at he
  linear_combination he

end LiquidDrop.CapacitaryK
