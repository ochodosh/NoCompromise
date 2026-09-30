module

public import NoCompromise.Capacity.LevelAsymptotics

@[expose] public section

/-!
# First derivative of the radial graph of small capacitary levels
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The derivative of normalization at a unit vector is the tangential projection. -/
lemma levelRadius_hasFDerivAt_direction {θ₀ : E₃} (h1 : ‖θ₀‖ = 1) :
    ∃ D : E₃ →L[ℝ] E₃, HasFDerivAt (fun y : E₃ => ‖y‖⁻¹ • y) D θ₀ ∧
      ∀ v : E₃, D v = v - ⟪θ₀, v⟫ • θ₀ := by
  have hsq := (hasStrictFDerivAt_norm_sq θ₀).hasFDerivAt
  have hs := hsq.sqrt (by simp [h1])
  have he : (fun y : E₃ => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [he] at hs
  have hinv := (hasDerivAt_inv (by simp [h1] : ‖θ₀‖ ≠ 0)).comp_hasFDerivAt θ₀ hs
  have hP := hinv.smul (hasFDerivAt_id θ₀)
  refine ⟨_, hP, fun v => ?_⟩
  simp [h1, innerSL_apply_apply]
  module

/-- Implicit differentiation of `u (ρ θ • θ / |θ|) = ε` at a unit vector. -/
lemma levelRadius_implicit_identity {u ρ : E₃ → ℝ} {θ₀ : E₃} {ε : ℝ} (h1 : ‖θ₀‖ = 1)
    (hρ : DifferentiableAt ℝ ρ θ₀) (hu : DifferentiableAt ℝ u (ρ θ₀ • θ₀))
    (hev : ∀ᶠ θ in 𝓝 θ₀, u (ρ θ • (‖θ‖⁻¹ • θ)) = ε) (v : E₃) :
    fderiv ℝ ρ θ₀ v * ⟪gradient u (ρ θ₀ • θ₀), θ₀⟫ +
      ρ θ₀ * ⟪gradient u (ρ θ₀ • θ₀), v - ⟪θ₀, v⟫ • θ₀⟫ = 0 := by
  obtain ⟨D, hD, hDv⟩ := levelRadius_hasFDerivAt_direction h1
  have hP0 : ‖θ₀‖⁻¹ • θ₀ = θ₀ := by rw [h1, inv_one, one_smul]
  have hΦ := hρ.hasFDerivAt.smul hD
  have hu' : HasFDerivAt u (fderiv ℝ u (ρ θ₀ • θ₀)) (ρ θ₀ • (‖θ₀‖⁻¹ • θ₀)) := by
    rw [hP0]; exact hu.hasFDerivAt
  have hG := hu'.comp θ₀ hΦ
  have hc : HasFDerivAt (fun θ => u (ρ θ • (‖θ‖⁻¹ • θ))) (0 : E₃ →L[ℝ] ℝ) θ₀ :=
    (hasFDerivAt_const ε θ₀).congr_of_eventuallyEq hev
  have h0 := congrArg (fun L : E₃ →L[ℝ] ℝ => L v) (hG.unique hc)
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, hDv, hP0,
    zero_apply, map_add, map_smul, smul_eq_mul] at h0
  simp only [← CapacitaryK.inner_gradient_eq_fderiv u] at h0
  linarith

/-- The implicit identity and the gradient expansion bound the derivative of the radius. -/
lemma levelRadius_fderiv_bound_core {Cinf C' ρ₀ a : ℝ} {θ₀ v g : E₃} (hC : 0 < Cinf)
    (h1 : ‖θ₀‖ = 1) (hρ₀ : 0 < ρ₀) (hsC : C' * ρ₀⁻¹ ≤ Cinf / 2)
    (hg : ‖g + (Cinf * ρ₀⁻¹ ^ 3) • (ρ₀ • θ₀)‖ ≤ C' * ρ₀⁻¹ ^ 3)
    (hid : a * ⟪g, θ₀⟫ + ρ₀ * ⟪g, v - ⟪θ₀, v⟫ • θ₀⟫ = 0) :
    |a| ≤ 4 * C' / Cinf * ‖v‖ := by
  set s := ρ₀⁻¹ with hs_def
  have hs : 0 < s := inv_pos.mpr hρ₀
  have hρs : ρ₀ * s = 1 := mul_inv_cancel₀ hρ₀.ne'
  clear_value s
  set e := g + (Cinf * s ^ 3) • (ρ₀ • θ₀) with he
  have hθθ : ⟪θ₀, θ₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
  have hge : g = e - (Cinf * s ^ 3) • (ρ₀ • θ₀) := by rw [he]; abel
  have hgr : ⟪g, θ₀⟫ = ⟪e, θ₀⟫ - Cinf * s ^ 2 := by
    rw [hge, inner_sub_left, inner_smul_left, inner_smul_left, hθθ]
    simp only [conj_trivial]
    linear_combination (-(Cinf * s ^ 2)) * hρs
  have hgT : ⟪g, v - ⟪θ₀, v⟫ • θ₀⟫ = ⟪e, v - ⟪θ₀, v⟫ • θ₀⟫ := by
    rw [hge, inner_sub_left, inner_smul_left, inner_smul_left]
    simp only [inner_sub_right, inner_smul_right, hθθ, conj_trivial]
    ring
  have hC' : 0 ≤ C' := by
    have := (norm_nonneg e).trans hg
    exact le_of_mul_le_mul_right (by rw [zero_mul]; exact this) (pow_pos hs 3)
  have her : |⟪e, θ₀⟫| ≤ C' * s ^ 3 := by
    calc _ ≤ ‖e‖ * ‖θ₀‖ := abs_real_inner_le_norm _ _
      _ ≤ C' * s ^ 3 := by rw [h1, mul_one]; exact hg
  have hvT : ‖v - ⟪θ₀, v⟫ • θ₀‖ ≤ 2 * ‖v‖ := by
    calc _ ≤ ‖v‖ + ‖⟪θ₀, v⟫ • θ₀‖ := norm_sub_le _ _
      _ = ‖v‖ + |⟪θ₀, v⟫| := by rw [norm_smul, h1, mul_one, Real.norm_eq_abs]
      _ ≤ ‖v‖ + ‖θ₀‖ * ‖v‖ := by gcongr; exact abs_real_inner_le_norm _ _
      _ = 2 * ‖v‖ := by rw [h1]; ring
  have heT : |⟪e, v - ⟪θ₀, v⟫ • θ₀⟫| ≤ C' * s ^ 3 * (2 * ‖v‖) := by
    calc _ ≤ ‖e‖ * ‖v - ⟪θ₀, v⟫ • θ₀‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul hg hvT (norm_nonneg _) (by positivity)
  have hlow : Cinf * s ^ 2 / 2 ≤ |⟪g, θ₀⟫| := by
    have h2 : C' * s ^ 3 ≤ Cinf / 2 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hsC (sq_nonneg s)
      have e' : C' * s ^ 3 = C' * s * s ^ 2 := by ring
      linarith
    rw [hgr, abs_sub_comm]
    have := abs_le.mp her
    rw [abs_of_pos (by nlinarith [sq_pos_of_pos hs, this.2])]
    linarith [this.2]
  have hkey : |a| * |⟪g, θ₀⟫| = ρ₀ * |⟪e, v - ⟪θ₀, v⟫ • θ₀⟫| := by
    have : a * ⟪g, θ₀⟫ = -(ρ₀ * ⟪g, v - ⟪θ₀, v⟫ • θ₀⟫) := by linarith
    rw [← abs_mul, this, abs_neg, abs_mul, abs_of_pos hρ₀, hgT]
  have hpos : 0 < Cinf * s ^ 2 / 2 := by positivity
  have hb : |a| * (Cinf * s ^ 2 / 2) ≤ 4 * C' / Cinf * ‖v‖ * (Cinf * s ^ 2 / 2) := by
    calc |a| * (Cinf * s ^ 2 / 2) ≤ |a| * |⟪g, θ₀⟫| :=
          mul_le_mul_of_nonneg_left hlow (abs_nonneg a)
      _ = ρ₀ * |⟪e, v - ⟪θ₀, v⟫ • θ₀⟫| := hkey
      _ ≤ ρ₀ * (C' * s ^ 3 * (2 * ‖v‖)) := mul_le_mul_of_nonneg_left heT hρ₀.le
      _ = 4 * C' / Cinf * ‖v‖ * (Cinf * s ^ 2 / 2) := by
          have e1 : ρ₀ * (C' * s ^ 3 * (2 * ‖v‖)) = 2 * C' * ‖v‖ * s ^ 2 * (ρ₀ * s) := by ring
          rw [e1, hρs]
          field_simp
          ring
  exact le_of_mul_le_mul_right hb hpos

/-- Blueprint `lem:level-asymptotics`: the small levels are radial graphs `r = ρ(θ)` with
`ρ = Cinf / ε + O(1)`, `w = ε² / Cinf + O(ε³)`, and first angular derivative of `ρ` bounded
uniformly in `ε` on the unit sphere (here `ρ` is `0`-homogeneous, `ρ θ = ρ (θ / |θ|)`).
`Cinf` is pinned by the value expansion. -/
theorem capacitary_level_radius_fderiv_bound
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ M) ∧
          {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} ∧
          (∀ x : E₃, u x = ε →
            gradient u x ≠ 0 ∧ |‖gradient u x‖ - ε ^ 2 / Cinf| ≤ M * ε ^ 3) ∧
          ∀ θ : E₃, ‖θ‖ = 1 → ‖fderiv ℝ ρ θ‖ ≤ M := by
  obtain ⟨Cinf, hC, ⟨R, C', hR, hexp⟩, ε₀, hε₀, -, M, hM⟩ :=
    capacitary_level_asymptotics hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = R + 2 * (|C'| + 1) / Cinf + 1 + |M| := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ := capacitary_potential_contDiffOn hK hu hh
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  refine ⟨Cinf, hC, ⟨R, C', hR, fun x hx => (hexp x hx).1⟩, min ε₀ (Cinf / T),
    lt_min hε₀ (div_pos hC hTpos), max M (4 * |C'| / Cinf), fun ε hε hεε₀ => ?_⟩
  have hε₀' : ε < ε₀ := hεε₀.trans_le (min_le_left _ _)
  have hεT : T < Cinf / ε := by
    have := hεε₀.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hε]; rw [lt_div_iff₀ hTpos] at this; linarith
  obtain ⟨⟨ρ, hρs, hρb, hρeq⟩, hpt, -, -⟩ := hM ε hε hε₀'
  have hMM : M ≤ max M (4 * |C'| / Cinf) := le_max_left _ _
  have hunit : ∀ θ : E₃, ‖θ‖ = 1 → R + 2 * (|C'| + 1) / Cinf + 1 ≤ ρ θ := by
    intro θ hθ
    have := (abs_le.mp (hρb θ hθ)).1
    have := le_abs_self M
    linarith
  have hunitpos : ∀ θ : E₃, ‖θ‖ = 1 → 0 < ρ θ := fun θ hθ =>
    lt_of_lt_of_le (by positivity) (hunit θ hθ)
  have hPP : ∀ θ : E₃, θ ≠ 0 → ‖‖θ‖⁻¹ • θ‖⁻¹ • (‖θ‖⁻¹ • θ) = ‖θ‖⁻¹ • θ := by
    intro θ hθ; rw [kelvin_norm_direction hθ, inv_one, one_smul]
  set ρ' : E₃ → ℝ := fun θ => ρ (‖θ‖⁻¹ • θ) with hρ'
  have hlev : ∀ θ : E₃, θ ≠ 0 → ρ' θ • (‖θ‖⁻¹ • θ) ∉ K ∧ u (ρ' θ • (‖θ‖⁻¹ • θ)) = ε := by
    intro θ hθ
    have hd := kelvin_norm_direction hθ
    have hp := hunitpos _ hd
    have hn : ‖ρ' θ • (‖θ‖⁻¹ • θ)‖ = ρ' θ := by
      rw [norm_smul, hd, mul_one, Real.norm_of_nonneg hp.le]
    have hmem : ρ' θ • (‖θ‖⁻¹ • θ) ∈ {x : E₃ | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} := by
      refine ⟨?_, ?_⟩
      · intro h0; rw [h0, norm_zero] at hn; exact hp.ne' hn.symm
      · rw [hn, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    rw [← hρeq] at hmem
    exact hmem
  have hdirsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E₃ => ‖y‖⁻¹ • y) {θ | θ ≠ 0} := fun θ hθ =>
    (((contDiffAt_id.norm ℝ hθ).inv (norm_ne_zero_iff.mpr hθ)).smul
      contDiffAt_id).contDiffWithinAt
  have hρ'sm : ContDiffOn ℝ (⊤ : ℕ∞) ρ' {θ | θ ≠ 0} :=
    hρs.comp hdirsm (fun θ hθ => by
      have := kelvin_norm_direction (show θ ≠ 0 from hθ)
      intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this)
  refine ⟨ρ', hρ'sm, fun θ hθ => ?_, ?_, fun x hx => ?_, fun θ₀ h1 => ?_⟩
  · simp only [hρ', hθ, inv_one, one_smul]
    exact (hρb θ hθ).trans hMM
  · rw [hρeq]
    ext x
    simp only [Set.mem_ofPred_eq, hρ']
    constructor
    · rintro ⟨hx0, hx⟩; exact ⟨hx0, by rw [hPP x hx0]; exact hx⟩
    · rintro ⟨hx0, hx⟩; exact ⟨hx0, by rw [hPP x hx0] at hx; exact hx⟩
  · obtain ⟨_, h2, _, h4, _⟩ := hpt x hx
    exact ⟨h2, h4.trans (mul_le_mul_of_nonneg_right hMM (by positivity))⟩
  -- the derivative bound
  have hθ0 : θ₀ ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hP0 : ‖θ₀‖⁻¹ • θ₀ = θ₀ := by rw [h1, inv_one, one_smul]
  have hρ0 : ρ' θ₀ = ρ θ₀ := by simp only [hρ', hP0]
  have hbig := hunit θ₀ h1
  rw [← hρ0] at hbig
  have hρ₀pos : 0 < ρ' θ₀ := lt_of_lt_of_le (by positivity) hbig
  obtain ⟨hx₀K, hx₀ε⟩ := hlev θ₀ hθ0
  rw [hP0] at hx₀K hx₀ε
  have hdiff : DifferentiableAt ℝ ρ' θ₀ :=
    (hρ'sm.contDiffAt (isOpen_ne.mem_nhds hθ0)).differentiableAt (by simp)
  have hudiff : DifferentiableAt ℝ u (ρ' θ₀ • θ₀) :=
    (hsm.contDiffAt (hopen.mem_nhds hx₀K)).differentiableAt (by simp)
  have hev : ∀ᶠ θ in 𝓝 θ₀, u (ρ' θ • (‖θ‖⁻¹ • θ)) = ε :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hθ0) (fun θ hθ => (hlev θ hθ).2)
  have hn₀ : ‖ρ' θ₀ • θ₀‖ = ρ' θ₀ := by
    rw [norm_smul, h1, mul_one, Real.norm_of_nonneg hρ₀pos.le]
  have hR' : R ≤ ‖ρ' θ₀ • θ₀‖ := by
    rw [hn₀]; have : 0 ≤ 2 * (|C'| + 1) / Cinf := by positivity
    linarith
  have hg := (hexp _ hR').2.1
  rw [hn₀] at hg
  simp only [div_eq_mul_inv, ← inv_pow] at hg
  have hsC : C' * (ρ' θ₀)⁻¹ ≤ Cinf / 2 := by
    have h2 : 2 * (|C'| + 1) / Cinf ≤ ρ' θ₀ := by linarith
    rw [div_le_iff₀ hC] at h2
    rw [mul_inv_le_iff₀ hρ₀pos]
    nlinarith [le_abs_self C', abs_nonneg C']
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hid := levelRadius_implicit_identity h1 hdiff hudiff hev v
  have hcore := levelRadius_fderiv_bound_core hC h1 hρ₀pos hsC hg hid
  rw [Real.norm_eq_abs]
  calc _ ≤ 4 * C' / Cinf * ‖v‖ := hcore
    _ ≤ 4 * |C'| / Cinf * ‖v‖ := by
        gcongr; exact le_abs_self C'
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)

end LiquidDrop
