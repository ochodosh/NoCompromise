import NoCompromise.Capacity.Kelvin
import NoCompromise.Capacity.LowerBarrier
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Positivity and radial level sets of capacitary potentials
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Blueprint `lem:kelvin`: every coefficient in a reciprocal-distance value
expansion is at least the radius of an interior ball. -/
theorem kelvin_coefficient_ge_of_lower_bound
    {u : E₃ → ℝ} {a Cinf R C' R₀ : ℝ}
    (hlower : ∀ x : E₃, R₀ < ‖x‖ → a / ‖x‖ ≤ u x)
    (hexp : ∀ x : E₃, R ≤ ‖x‖ → |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2) :
    a ≤ Cinf := by
  by_contra h
  have hd : 0 < a - Cinf := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨t, ht⟩ := exists_gt (max (max R R₀) (max 0 (C' / (a - Cinf))))
  have ht0 : 0 < t := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htR : R ≤ t := (le_trans (le_max_left _ _) (le_max_left _ _)).trans ht.le
  have htR₀ : R₀ < t := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htC : C' / (a - Cinf) < t := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  obtain ⟨x, hx⟩ := exists_norm_eq E₃ ht0.le
  have hl := hlower x (hx ▸ htR₀)
  have he := (abs_le.mp (hexp x (hx ▸ htR))).2
  rw [hx] at hl he
  have hle : (a - Cinf) / t ≤ C' / t ^ 2 := by
    rw [sub_div]
    linarith
  have hm := (div_le_div_iff₀ ht0 (sq_pos_of_pos ht0)).mp hle
  have hlt := (div_lt_iff₀ hd).mp htC
  nlinarith

/-- Blueprint `lem:kelvin`: the Kelvin expansion has a strictly positive
coefficient under precisely the capacitary-potential hypotheses. -/
theorem kelvin_expansion_pos
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧ ∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 := by
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  obtain ⟨Cinf, R, C', hR, hexp⟩ := kelvin_expansion hK hR₀ hKR hzero hu hh hb hinf
  have hl := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  have haC : a ≤ Cinf := kelvin_coefficient_ge_of_lower_bound
    (R₀ := R₀) (R := R) (C' := C') (fun x hx => hl x (by
      intro hxK
      have hxR : ‖x‖ ≤ R₀ := by simpa using hKR hxK
      exact (not_lt_of_ge hxR) hx)) (fun x hx => (hexp x hx).1)
  exact ⟨Cinf, ha.trans_le haC, R, C', hR, hexp⟩

/-- Blueprint `lem:level-asymptotics`: the derivative along a ray is the
inner product of its direction with the genuine Fréchet gradient. -/
lemma hasDerivAt_capacitary_ray {u : E₃ → ℝ} {θ : E₃} {t : ℝ}
    (hu : DifferentiableAt ℝ u (t • θ)) :
    HasDerivAt (fun s : ℝ => u (s • θ)) (inner ℝ θ (gradient u (t • θ))) t := by
  rw [inner_gradient_right, conj_trivial]
  convert! hu.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const θ) using 1
  simp

/-- Blueprint `lem:level-asymptotics`: a positive Kelvin coefficient forces a
uniformly negative radial derivative outside a sufficiently large sphere. -/
theorem kelvin_radial_derivative_neg
    {u : E₃ → ℝ} {Cinf R C' R₀ : ℝ} (hC : 0 < Cinf)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u {x | R₀ < ‖x‖})
    (hexp : ∀ x : E₃, R ≤ ‖x‖ →
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ R ≤ R₁ ∧ R₀ < R₁ ∧
      ∀ θ : E₃, ‖θ‖ = 1 → ∀ t : ℝ, R₁ ≤ t →
        HasDerivAt (fun s : ℝ => u (s • θ)) (inner ℝ θ (gradient u (t • θ))) t ∧
        inner ℝ θ (gradient u (t • θ)) ≤ -Cinf / (2 * t ^ 2) ∧
        -Cinf / (2 * t ^ 2) < 0 := by
  obtain ⟨R₁, hR₁⟩ := exists_gt (max (max R R₀) (max 0 (2 * C' / Cinf)))
  have hpos : 0 < R₁ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hR₁
  have hR : R ≤ R₁ := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hR₁.le
  have hR₀ : R₀ < R₁ := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_left _ _)) hR₁
  have hbound : 2 * C' / Cinf ≤ R₁ :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hR₁.le
  refine ⟨R₁, hpos, hR, hR₀, ?_⟩
  intro θ hθ t ht
  have ht0 : 0 < t := hpos.trans_le ht
  have hnorm : ‖t • θ‖ = t := by rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg ht0.le]
  have hdiff := (hs.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds
    (show R₀ < ‖t • θ‖ by rw [hnorm]; exact hR₀.trans_le ht))).differentiableAt (by simp)
  refine ⟨hasDerivAt_capacitary_ray hdiff, ?_,
    div_neg_of_neg_of_pos (neg_neg_of_pos hC) (by positivity)⟩
  have hi := (real_inner_le_norm θ
    (gradient u (t • θ) + (Cinf / ‖t • θ‖ ^ 3) • (t • θ))).trans
    (by simpa only [hθ, one_mul] using hexp (t • θ) (by rw [hnorm]; exact hR.trans ht))
  rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hθ, one_pow, mul_one, hnorm] at hi
  have hct : 2 * C' ≤ t * Cinf := (div_le_iff₀ hC).mp (hbound.trans ht)
  have ht3 : 0 < t ^ 3 := pow_pos ht0 3
  have hie := (le_div_iff₀ ht3).mp hi
  have he : Cinf / t ^ 3 * t * t ^ 3 = Cinf * t := by field_simp
  rw [add_mul, he] at hie
  apply (le_div_iff₀ (show 0 < 2 * t ^ 2 by positivity)).mpr
  nlinarith [mul_pos ht0 hC]

/-- Blueprint `lem:level-asymptotics`: the negative radial derivative gives
strict decrease on the entire exterior ray. -/
lemma strictAntiOn_capacitary_ray {u : E₃ → ℝ} (hu : Continuous u)
    {θ : E₃} {R : ℝ}
    (hd : ∀ t : ℝ, R ≤ t →
      HasDerivAt (fun s : ℝ => u (s • θ)) (inner ℝ θ (gradient u (t • θ))) t ∧
      inner ℝ θ (gradient u (t • θ)) < 0) :
    StrictAntiOn (fun t : ℝ => u (t • θ)) (Ici R) := by
  apply strictAntiOn_of_deriv_neg (f := fun t : ℝ => u (t • θ)) (convex_Ici R)
    (hu.comp (continuous_id.smul continuous_const)).continuousOn
  intro t ht
  obtain ⟨hdt, hneg⟩ := hd t (interior_subset ht)
  rw [hdt.deriv]
  exact hneg

/-- Blueprint `lem:level-asymptotics`: each sufficiently small positive value
is attained exactly once on a strictly decreasing exterior unit ray. -/
lemma existsUnique_capacitary_ray_level {u : E₃ → ℝ} (hu : Continuous u)
    (hinf : Tendsto u (cocompact E₃) (𝓝 0)) {θ : E₃} (hθ : ‖θ‖ = 1)
    {R ε : ℝ} (hε : 0 < ε) (hstart : ε < u (R • θ))
    (hanti : StrictAntiOn (fun t : ℝ => u (t • θ)) (Ici R)) :
    ∃! t : ℝ, R < t ∧ u (t • θ) = ε := by
  have hray : Tendsto (fun t : ℝ => t • θ) atTop (cocompact E₃) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simpa only [norm_smul, hθ, mul_one, Real.norm_eq_abs] using tendsto_abs_atTop_atTop
  have hsmall := ((hinf.comp hray).eventually (gt_mem_nhds hε))
  obtain ⟨b, hbR, hb⟩ := (hsmall.and (eventually_gt_atTop R)).exists
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hb.le
    (hu.comp (continuous_id.smul continuous_const)).continuousOn
    (show ε ∈ Icc (u (b • θ)) (u (R • θ)) from ⟨hbR.le, hstart.le⟩)
  change u (t • θ) = ε at he
  have hRt : R < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have : u (t • θ) = u (R • θ) := congrArg (fun s => u (s • θ)) heq.symm
    linarith)
  refine ⟨t, ⟨hRt, he⟩, ?_⟩
  intro s hs
  exact hanti.injOn hs.1.le ht.1 (hs.2.trans he.symm)

/-- Blueprint `lem:level-asymptotics`: normalization has unit length away
from the origin. -/
lemma kelvin_norm_direction {θ : E₃} (hθ : θ ≠ 0) : ‖‖θ‖⁻¹ • θ‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hθ)]

/-- Blueprint `lem:level-asymptotics`: normalized directions depend
continuously on every nonzero vector. -/
lemma kelvin_direction_continuousAt {θ : E₃} (hθ : θ ≠ 0) :
    ContinuousAt (fun y : E₃ => ‖y‖⁻¹ • y) θ :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hθ)).smul continuousAt_id

/-- Blueprint `lem:level-asymptotics`: the unique exterior ray radius is
continuous in the direction, using strict decrease and continuity of the potential. -/
lemma kelvin_ray_radius_continuousOn {u : E₃ → ℝ} (hu : Continuous u)
    {R ε : ℝ} {ρ : E₃ → ℝ}
    (hρ : ∀ θ : E₃, θ ≠ 0 → R < ρ θ ∧ u (ρ θ • (‖θ‖⁻¹ • θ)) = ε)
    (hanti : ∀ θ : E₃, ‖θ‖ = 1 → StrictAntiOn (fun t : ℝ => u (t • θ)) (Ici R)) :
    ContinuousOn ρ {θ : E₃ | θ ≠ 0} := by
  intro θ hθ
  apply ContinuousAt.continuousWithinAt
  apply tendsto_order.mpr
  constructor
  · intro l hl
    by_cases hlR : l ≤ R
    · filter_upwards [isOpen_ne.mem_nhds hθ] with y hy
      exact hlR.trans_lt (hρ y hy).1
    · have hRl : R ≤ l := (lt_of_not_ge hlR).le
      have hlε : ε < u (l • (‖θ‖⁻¹ • θ)) := by
        rw [← (hρ θ hθ).2]
        exact hanti _ (kelvin_norm_direction hθ) hRl (hρ θ hθ).1.le hl
      have hc : ContinuousAt (fun y : E₃ => u (l • (‖y‖⁻¹ • y))) θ :=
        hu.continuousAt.comp ((kelvin_direction_continuousAt hθ).const_smul l)
      filter_upwards [hc.eventually (lt_mem_nhds hlε), isOpen_ne.mem_nhds hθ] with y hyε hy
      apply lt_of_not_ge
      intro hyl
      have hle := (hanti _ (kelvin_norm_direction hy)).antitoneOn (hρ y hy).1.le hRl hyl
      rw [(hρ y hy).2] at hle
      exact (not_le_of_gt hyε) hle
  · intro r hr
    have hRr : R ≤ r := (hρ θ hθ).1.le.trans hr.le
    have hrε : u (r • (‖θ‖⁻¹ • θ)) < ε := by
      rw [← (hρ θ hθ).2]
      exact hanti _ (kelvin_norm_direction hθ) (hρ θ hθ).1.le hRr hr
    have hc : ContinuousAt (fun y : E₃ => u (r • (‖y‖⁻¹ • y))) θ :=
      hu.continuousAt.comp ((kelvin_direction_continuousAt hθ).const_smul r)
    filter_upwards [hc.eventually_lt_const hrε, isOpen_ne.mem_nhds hθ] with y hyε hy
    apply lt_of_not_ge
    intro hry
    have hle := (hanti _ (kelvin_norm_direction hy)).antitoneOn hRr (hρ y hy).1.le hry
    rw [(hρ y hy).2] at hle
    exact (not_le_of_gt hyε) hle

/-- Blueprint `lem:level-asymptotics`: the unique exterior ray radius is
smooth wherever the radial derivative is negative, by the implicit function theorem. -/
lemma kelvin_ray_radius_contDiffOn {u : E₃ → ℝ} {R R₀ ε : ℝ} {ρ : E₃ → ℝ}
    (hR : 0 < R) (hR₀ : R₀ < R)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u {x | R₀ < ‖x‖})
    (hρ : ∀ θ : E₃, θ ≠ 0 → R < ρ θ ∧ u (ρ θ • (‖θ‖⁻¹ • θ)) = ε)
    (hanti : ∀ θ : E₃, ‖θ‖ = 1 → StrictAntiOn (fun t : ℝ => u (t • θ)) (Ici R))
    (hneg : ∀ θ : E₃, ‖θ‖ = 1 → ∀ t : ℝ, R < t →
      inner ℝ θ (gradient u (t • θ)) < 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} := by
  intro θ hθ
  have hpos : 0 < ρ θ := hR.trans (hρ θ hθ).1
  have hn : ‖ρ θ • (‖θ‖⁻¹ • θ)‖ = ρ θ := by
    rw [norm_smul, kelvin_norm_direction hθ, mul_one, Real.norm_of_nonneg hpos.le]
  have hU := hs.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds
    (show R₀ < ‖ρ θ • (‖θ‖⁻¹ • θ)‖ by rw [hn]; exact hR₀.trans (hρ θ hθ).1))
  have hdir : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E₃ => ‖y‖⁻¹ • y) θ :=
    ((contDiffAt_id.norm ℝ hθ).inv (norm_ne_zero_iff.mpr hθ)).smul contDiffAt_id
  let F : E₃ × ℝ → ℝ := fun p => u (p.2 • (‖p.1‖⁻¹ • p.1))
  have hfst : ContDiffAt ℝ (⊤ : ℕ∞) (Prod.fst : E₃ × ℝ → E₃) (θ, ρ θ) := contDiffAt_fst
  have hdp := hdir.comp (θ, ρ θ) hfst
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : E₃ × ℝ => p.2 • (‖p.1‖⁻¹ • p.1)) (θ, ρ θ) :=
    contDiffAt_snd.smul hdp
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F (θ, ρ θ) := hU.comp (θ, ρ θ) hmap
  have hp : HasFDerivAt (fun t : ℝ => F (θ, t))
      (fderiv ℝ F (θ, ρ θ) ∘L ContinuousLinearMap.inr ℝ E₃ ℝ) (ρ θ) := by
    convert! (hF.differentiableAt (by simp)).hasFDerivAt.comp (ρ θ)
      ((hasFDerivAt_const θ (ρ θ)).prodMk (hasFDerivAt_id (ρ θ))) using 1
  have hd := hasDerivAt_capacitary_ray (hU.differentiableAt (by simp))
  have hdne := (hneg _ (kelvin_norm_direction hθ) _ (hρ θ hθ).1).ne
  have hi : (fderiv ℝ F (θ, ρ θ) ∘L ContinuousLinearMap.inr ℝ E₃ ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hdne), ?_⟩
    exact (hd.hasFDerivAt_equiv hdne).unique hp
  let ψ := hF.implicitFunction (by simp) hi
  have hψself : ψ θ = ρ θ := hF.implicitFunction_apply_self (by simp) hi
  have hψsmooth : ContDiffAt ℝ (⊤ : ℕ∞) ψ θ := hF.contDiffAt_implicitFunction (by simp) hi
  have he : ρ =ᶠ[𝓝 θ] ψ := by
    have hψR : ∀ᶠ y in 𝓝 θ, R < ψ y :=
      hψsmooth.continuousAt.eventually (lt_mem_nhds (by rw [hψself]; exact (hρ θ hθ).1))
    filter_upwards [hF.eventually_apply_implicitFunction (by simp) hi, hψR,
      isOpen_ne.mem_nhds hθ] with y hy hyR hy0
    apply (hanti _ (kelvin_norm_direction hy0)).injOn (hρ y hy0).1.le hyR.le
    change u (ρ y • (‖y‖⁻¹ • y)) = u (ψ y • (‖y‖⁻¹ • y))
    change u (ψ y • (‖y‖⁻¹ • y)) = u (ρ θ • (‖θ‖⁻¹ • θ)) at hy
    rw [(hρ y hy0).2, hy, (hρ θ hθ).2]
  exact (hψsmooth.congr_of_eventuallyEq he).contDiffWithinAt

/-- Blueprint `lem:level-asymptotics`: the value expansion and lower barrier
bound the radius error uniformly, with explicit constant `C' / a`. -/
lemma kelvin_level_radius_estimate {a Cinf C' ε t : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (ht : 0 < t)
    (hlower : a / t ≤ ε) (hexp : |ε - Cinf / t| ≤ C' / t ^ 2) :
    |t - Cinf / ε| ≤ C' / a := by
  have hC' : 0 ≤ C' := by
    have h := (le_div_iff₀ (sq_pos_of_pos ht)).mp ((abs_nonneg _).trans hexp)
    simpa using h
  have he : t - Cinf / ε = (ε - Cinf / t) * (t / ε) := by field_simp
  rw [he, abs_mul, abs_of_pos (div_pos ht hε)]
  calc
    _ ≤ (C' / t ^ 2) * (t / ε) := mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = C' / (ε * t) := by field_simp
    _ ≤ C' / a := div_le_div_of_nonneg_left hC' ha ((div_le_iff₀ ht).mp hlower)

/-- Blueprint `lem:level-asymptotics`: small exterior levels are smooth
radial graphs with a uniform radius error. The positive coefficient and both
expansion estimates are explicit hypotheses, ensuring the same Kelvin coefficient
occurs in the radius asymptotics. -/
theorem capacitary_level_radial_graph_of_expansion
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ}
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0))
    {Cinf R C' : ℝ} (hC : 0 < Cinf)
    (hexp : ∀ x : E₃, R ≤ ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C'' : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
        (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ C'') ∧
        {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} := by
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hlower := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  obtain ⟨R₁, hR₁, hRR₁, hR₀R₁, hd⟩ := kelvin_radial_derivative_neg hC
    (capacitary_potential_contDiffOn_exterior hK hKR hu hh) (fun x hx => (hexp x hx).2)
  have hout : ∀ x : E₃, R₁ ≤ ‖x‖ → x ∉ K := by
    intro x hx hxK
    have hxR : ‖x‖ ≤ R₀ := by simpa using hKR hxK
    linarith
  have hanti : ∀ θ : E₃, ‖θ‖ = 1 →
      StrictAntiOn (fun t : ℝ => u (t • θ)) (Ici R₁) := by
    intro θ hθ
    exact strictAntiOn_capacitary_ray hu (fun t ht =>
      ⟨(hd θ hθ t ht).1, (hd θ hθ t ht).2.1.trans_lt (hd θ hθ t ht).2.2⟩)
  refine ⟨a / R₁, div_pos ha hR₁, C' / a, ?_⟩
  intro ε hε hε₀
  have hroots : ∀ θ : E₃, ‖θ‖ = 1 → ∃! t : ℝ, R₁ < t ∧ u (t • θ) = ε := by
    intro θ hθ
    have hn : ‖R₁ • θ‖ = R₁ := by
      rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg hR₁.le]
    have hl := hlower (R₁ • θ) (hout _ (by rw [hn]))
    rw [hn] at hl
    exact existsUnique_capacitary_ray_level hu hinf hθ hε (hε₀.trans_le hl) (hanti θ hθ)
  let ρ : E₃ → ℝ := fun θ => if hθ : θ ≠ 0 then
    Classical.choose (hroots (‖θ‖⁻¹ • θ) (kelvin_norm_direction hθ)) else 0
  have hρ : ∀ θ : E₃, θ ≠ 0 → R₁ < ρ θ ∧ u (ρ θ • (‖θ‖⁻¹ • θ)) = ε := by
    intro θ hθ
    dsimp [ρ]
    rw [dite_eq_left hθ]
    exact (Classical.choose_spec (hroots _ (kelvin_norm_direction hθ))).1
  have hunit : ∀ θ : E₃, ‖θ‖ = 1 → R₁ < ρ θ ∧ u (ρ θ • θ) = ε := by
    intro θ hθ
    have hθ0 : θ ≠ 0 := by intro he; simp [he] at hθ
    simpa only [hθ, inv_one, one_smul] using hρ θ hθ0
  refine ⟨ρ, kelvin_ray_radius_contDiffOn hR₁ hR₀R₁
    (capacitary_potential_contDiffOn_exterior hK hKR hu hh) hρ hanti
    (fun θ hθ t ht => (hd θ hθ t ht.le).2.1.trans_lt (hd θ hθ t ht.le).2.2), ?_, ?_⟩
  · intro θ hθ
    obtain ⟨hr, he⟩ := hunit θ hθ
    have hr0 : 0 < ρ θ := hR₁.trans hr
    have hn : ‖ρ θ • θ‖ = ρ θ := by
      rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg hr0.le]
    have hl := hlower (ρ θ • θ) (hout _ (by rw [hn]; exact hr.le))
    have hv := (hexp (ρ θ • θ) (by rw [hn]; exact hRR₁.trans hr.le)).1
    rw [hn, he] at hl hv
    exact kelvin_level_radius_estimate ha hε hr0 hl hv
  · ext x
    constructor
    · rintro ⟨hxK, hxε⟩
      have hx0 : x ≠ 0 := by intro he; exact hxK (he ▸ interior_subset hzero)
      have hn0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hl := hlower x hxK
      rw [hxε] at hl
      have hlarge : R₁ < ‖x‖ := by
        have h := (div_lt_div_iff₀ hn0 hR₁).mp (hl.trans_lt hε₀)
        nlinarith
      have hdir := kelvin_norm_direction hx0
      have hrecon : ‖x‖ • (‖x‖⁻¹ • x) = x := by
        rw [smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
      refine ⟨hx0, ?_⟩
      apply (hanti _ hdir).injOn hlarge.le (hunit _ hdir).1.le
      dsimp only
      rw [hrecon, hxε, (hunit _ hdir).2]
    · rintro ⟨hx0, hxρ⟩
      have hdir := kelvin_norm_direction hx0
      obtain ⟨hr, he⟩ := hunit _ hdir
      rw [← hxρ] at hr he
      have hrecon : ‖x‖ • (‖x‖⁻¹ • x) = x := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
      rw [hrecon] at he
      exact ⟨hout x hr.le, he⟩

/-- Blueprint `lem:level-asymptotics`: the positive Kelvin expansion and
smooth radial graphs for all sufficiently small levels, using one and the same
coefficient in both the expansion and the uniform radius asymptotics. -/
theorem capacitary_level_radial_graph
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, 0 < Cinf ∧
      (∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
        ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C'' : ℝ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ ρ : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) ρ {θ | θ ≠ 0} ∧
          (∀ θ : E₃, ‖θ‖ = 1 → |ρ θ - Cinf / ε| ≤ C'') ∧
          {x | x ∉ K ∧ u x = ε} = {x | x ≠ 0 ∧ ‖x‖ = ρ (‖x‖⁻¹ • x)} := by
  obtain ⟨Cinf, hC, R, C', hR, hexp⟩ := kelvin_expansion_pos hK hR₀ hKR hzero hu hh hb hinf
  exact ⟨Cinf, hC, ⟨R, C', hR, hexp⟩,
    capacitary_level_radial_graph_of_expansion hK hKR hzero hu hh hb hinf hC hexp⟩

end LiquidDrop
