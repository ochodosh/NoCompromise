module

public import NoCompromise.CapacitaryK.LevelGradSecondDerivative
public import NoCompromise.CapacitaryK.LevelAreaSecondDerivative

@[expose] public section

/-!
# Spatial calculus for the gradient-length remainder

The spatial error is smooth in the far field. The radial decomposition below
isolates its linear harmonic remainder and its quadratic tangential correction.
-/

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Smoothness of a gradient norm wherever its gradient is nonzero. -/
theorem levelGradDecay_gradNorm_contDiffAt {U : E3 → ℝ} {x : E3}
    (hU : ContDiffAt ℝ (⊤ : ℕ∞) U x) (hg : 0 < gradNorm U x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (gradNorm U) x := by
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) (gradient U) x :=
    (toDual ℝ E3).symm.contDiff.contDiffAt.comp x (hU.fderiv_right (by simp))
  exact hG.norm ℝ (norm_pos_iff.mp hg)

/-- The gradient-length remainder is smooth outside a sufficiently large ball,
for any positive-monopole expansion with the stated first remainder derivative. -/
theorem levelGradDecay_spatial_smooth {u v : E3 → ℝ} {R M : ℝ}
    (hC : 0 < v 0)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R < ‖x‖})
    (hDW : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (kelvinTranslatedRemainder u v) x‖ ≤ M / ‖x‖ ^ 5) :
    ∃ R' : ℝ, R < R' ∧ 1 ≤ R' ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (levelGradSecond_spatialRemainder u v)
        {x | R' < ‖x‖} := by
  let U : E3 → ℝ := fun x => u (x + (v 0)⁻¹ • gradient v 0)
  let S := max R 1
  have hs : ∀ x : E3, S < ‖x‖ → x ≠ 0 := by
    intro x hx
    exact norm_pos_iff.mp ((zero_lt_one.trans_le (le_max_right R 1)).trans hx)
  have hU : ContDiffOn ℝ (⊤ : ℕ∞) U {x | S < ‖x‖} := by
    apply (isOpen_lt continuous_const continuous_norm).contDiffOn_iff.mpr
    intro x hx
    have he : U = fun y =>
        (v 0 / ‖y‖ + farQuadrupole (kelvinTranslatedQuadrupole v) y) +
          kelvinTranslatedRemainder u v y := by
      funext y
      dsimp [U, farQuadrupole, kelvinTranslatedRemainder]
      ring
    rw [he]
    exact ((contDiffAt_monopole (v 0) (hs x hx)).add
      (contDiffAt_farQuadrupole (translated_quadrupole_contDiff v) (hs x hx))).add
        (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds
          ((le_max_left R 1).trans_lt hx)))
  obtain ⟨R', hR', hb⟩ := gradNorm_far_lower_bound hC hU
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v)
    (fun x hx => hDW x ((le_max_left R 1).trans hx))
  refine ⟨max R' (S + 1), ?_, ?_, ?_⟩
  · have := le_max_right R' (S + 1)
    have := le_max_left R 1
    dsimp only [S] at *
    linarith
  · exact (le_max_right R 1).trans ((le_add_of_nonneg_right zero_le_one).trans
      (le_max_right R' (S + 1)))
  · apply (isOpen_lt continuous_const continuous_norm).contDiffOn_iff.mpr
    intro x hx
    have hxS : S < ‖x‖ := by
      have := (le_max_right R' (S + 1)).trans_lt hx
      linarith
    have hpos := (hb x ((le_max_left R' (S + 1)).trans hx.le)).2
    have hGN : gradNorm U = fun y => gradNorm u (y + (v 0)⁻¹ • gradient v 0) := by
      funext y
      simp only [gradNorm, U, gradient, fderiv_comp_add_right]
    have hgn := levelGradDecay_gradNorm_contDiffAt
      (hU.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hxS)) hpos
    rw [hGN] at hgn
    have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E3 => ‖y‖⁻¹) x :=
      (contDiffAt_id.norm ℝ (hs x hxS)).inv (norm_ne_zero_iff.mpr (hs x hxS))
    exact (hgn.sub (contDiffAt_const.mul (hn.pow 2))).sub
      ((contDiffAt_const.mul (translated_quadrupole_contDiff v).contDiffAt).mul (hn.pow 6))

/-- The original capacitary hypotheses imply far-field smoothness of the spatial
gradient-length remainder for the Kelvin extension supplied by the derivative theorem. -/
theorem levelGradDecay_capacitary_spatial_smooth
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ R : ℝ, 1 ≤ R ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (levelGradSecond_spatialRemainder u v) {x | R < ‖x‖} := by
  obtain ⟨v, r, hr, hv, he, hv0, R, M, _, _, hW, hD⟩ :=
    levelGradSecond_capacitary_translated_remainder_derivatives
      hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨R', _, hR', hs⟩ := levelGradDecay_spatial_smooth hv0 hW
    (fun x hx => (hD x hx).2.1)
  exact ⟨v, r, hr, hv, he, hv0, R', hR', hs⟩

/-- A common bound for a function and its first two derivatives at one point. -/
structure levelGradDecay_JetBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E3 → F) (x : E3) (B : ℝ) : Prop where
  smooth : ContDiffAt ℝ 2 f x
  value : ‖f x‖ ≤ B
  first : ‖fderiv ℝ f x‖ ≤ B
  second : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B

/-- Enlarging a common jet bound preserves it. -/
theorem levelGradDecay_jet_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E3 → F} {x : E3} {A B : ℝ} (hf : levelGradDecay_JetBound f x A)
    (hAB : A ≤ B) : levelGradDecay_JetBound f x B :=
  ⟨hf.smooth, hf.value.trans hAB, hf.first.trans hAB, hf.second.trans hAB⟩

/-- Jet bounds are unchanged by replacing a function by a germ-equal function. -/
theorem levelGradDecay_jet_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E3 → F} {x : E3} {B : ℝ} (hf : levelGradDecay_JetBound f x B)
    (he : g =ᶠ[𝓝 x] f) : levelGradDecay_JetBound g x B := by
  refine ⟨hf.smooth.congr_of_eventuallyEq he, ?_, ?_, ?_⟩
  · simpa only [he.eq_of_nhds] using hf.value
  · simpa only [he.fderiv_eq] using hf.first
  · simpa only [he.fderiv.fderiv_eq] using hf.second

set_option maxSynthPendingDepth 8 in
-- The codomain may itself be a space of nested continuous linear maps.
/-- Constant scalar multiplication preserves the common jet bound. -/
theorem levelGradDecay_jet_const_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F} {x : E3} {B : ℝ}
    (hf : levelGradDecay_JetBound f x B) (c : ℝ) :
    levelGradDecay_JetBound (fun y => c • f y) x (|c| * B) := by
  refine ⟨hf.smooth.const_smul c, ?_, ?_, ?_⟩
  · simpa only [norm_smul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left hf.value (abs_nonneg c)
  · change ‖fderiv ℝ (c • f) x‖ ≤ _
    rw [fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hf.first (abs_nonneg c)
  · change ‖fderiv ℝ (fderiv ℝ (c • f)) x‖ ≤ _
    rw [fderiv_const_smul_field, fderiv_const_smul_field, Pi.smul_apply,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hf.second (abs_nonneg c)

/-- Additivity of the second derivative for vector-valued functions. -/
theorem levelGradDecay_fderiv_two_add {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E3 → F} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y + fderiv ℝ g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact fderiv_fun_add (hy.differentiableAt (by norm_num))
      (hz.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_fun_add
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)

/-- The sum of common jet bounds bounds a sum. -/
theorem levelGradDecay_jet_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E3 → F} {x : E3} {A B : ℝ} (hf : levelGradDecay_JetBound f x A)
    (hg : levelGradDecay_JetBound g x B) :
    levelGradDecay_JetBound (fun y => f y + g y) x (A + B) := by
  refine ⟨hf.smooth.add hg.smooth,
    (norm_add_le _ _).trans (add_le_add hf.value hg.value), ?_, ?_⟩
  · rw [fderiv_fun_add (hf.smooth.differentiableAt (by norm_num))
      (hg.smooth.differentiableAt (by norm_num))]
    exact (norm_add_le _ _).trans (add_le_add hf.first hg.first)
  · rw [levelGradDecay_fderiv_two_add hf.smooth hg.smooth]
    exact (norm_add_le (fderiv ℝ (fderiv ℝ f) x)
      (fderiv ℝ (fderiv ℝ g) x)).trans (add_le_add hf.second hg.second)

/-- A scalar-vector product has a common jet bound with four product-rule terms. -/
theorem levelGradDecay_jet_smul {a : E3 → ℝ} {V : E3 → E3} {x : E3} {A B : ℝ}
    (ha : levelGradDecay_JetBound a x A) (hV : levelGradDecay_JetBound V x B) :
    levelGradDecay_JetBound (fun y => a y • V y) x (4 * A * B) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha.value
  have hB : 0 ≤ B := (norm_nonneg _).trans hV.value
  obtain ⟨hD, hDD⟩ := levelAreaSecond_smul_bounds ha.smooth hV.smooth
  have ha0 : |a x| ≤ A := ha.value
  refine ⟨ha.smooth.smul hV.smooth, ?_, hD.trans ?_, hDD.trans ?_⟩
  · rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul ha0 hV.value (norm_nonneg _) hA).trans (by nlinarith)
  · calc
      _ ≤ A * B + A * B := by
        gcongr
        · exact hV.first
        · exact ha.first
        · exact hV.value
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ A * B + 2 * A * B + A * B := by
        gcongr
        · exact hV.second
        · exact ha.first
        · exact hV.first
        · exact ha.second
        · exact hV.value
      _ = _ := by ring

/-- A scalar product has the same four-term common jet bound. -/
theorem levelGradDecay_jet_mul {a b : E3 → ℝ} {x : E3} {A B : ℝ}
    (ha : levelGradDecay_JetBound a x A) (hb : levelGradDecay_JetBound b x B) :
    levelGradDecay_JetBound (fun y => a y * b y) x (4 * A * B) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha.value
  have hB : 0 ≤ B := (norm_nonneg _).trans hb.value
  have ha0 : |a x| ≤ A := ha.value
  have hb0 : |b x| ≤ B := hb.value
  refine ⟨ha.smooth.mul hb.smooth, ?_, ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul ha.value hb.value (norm_nonneg _) hA).trans (by nlinarith)
  · change ‖fderiv ℝ (a * b) x‖ ≤ _
    rw [((ha.smooth.differentiableAt (by norm_num)).hasFDerivAt.mul
      (hb.smooth.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ A * B + B * A := by
        gcongr
        · exact hb.first
        · exact ha.first
      _ ≤ _ := by nlinarith
  · apply (levelAreaSecond_fderiv_two_mul_bound ha.smooth hb.smooth).trans
    calc
      _ ≤ A * B + 2 * A * B + A * B := by
        gcongr
        · exact hb.second
        · exact ha.first
        · exact hb.first
        · exact ha.second
      _ = _ := by ring

/-- The second product rule for a real inner product. -/
theorem levelGradDecay_fderiv_two_inner {V W : E3 → E3} {x : E3}
    (hV : ContDiffAt ℝ 2 V x) (hW : ContDiffAt ℝ 2 W x) (e f : E3) :
    fderiv ℝ (fderiv ℝ (fun y => ⟪V y, W y⟫)) x e f =
      ⟪V x, fderiv ℝ (fderiv ℝ W) x e f⟫ +
        ⟪fderiv ℝ V x e, fderiv ℝ W x f⟫ +
        ⟪fderiv ℝ V x f, fderiv ℝ W x e⟫ +
        ⟪fderiv ℝ (fderiv ℝ V) x e f, W x⟫ := by
  have hVd := hV.differentiableAt (by norm_num)
  have hWd := hW.differentiableAt (by norm_num)
  have hDV := (hV.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDW := (hW.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDc := ((hV.inner ℝ hW).fderiv_right (m := 1)
    (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => fderiv ℝ (fun z => ⟪V z, W z⟫) y f) =ᶠ[𝓝 x]
      (fun y => ⟪V y, fderiv ℝ W y f⟫ + ⟪fderiv ℝ V y f, W y⟫) := by
    filter_upwards [hV.eventually (by norm_num), hW.eventually (by norm_num)] with y hy hz
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.inner ℝ
      (hz.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  have hleft := hDc.hasFDerivAt.clm_apply (hasFDerivAt_const f x)
  have hright := (hVd.hasFDerivAt.inner ℝ
    (hDW.hasFDerivAt.clm_apply (hasFDerivAt_const f x))).add
      ((hDV.hasFDerivAt.clm_apply (hasFDerivAt_const f x)).inner ℝ hWd.hasFDerivAt)
  have hid := congrArg (fun L : E3 →L[ℝ] ℝ => L e)
    ((hleft.congr_of_eventuallyEq heq.symm).unique hright)
  simpa [add_assoc] using hid

/-- Inner products preserve common jet bounds, with the four-term product constant. -/
theorem levelGradDecay_jet_inner {V W : E3 → E3} {x : E3} {A B : ℝ}
    (hV : levelGradDecay_JetBound V x A) (hW : levelGradDecay_JetBound W x B) :
    levelGradDecay_JetBound (fun y => ⟪V y, W y⟫) x (4 * A * B) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hV.value
  have hB : 0 ≤ B := (norm_nonneg _).trans hW.value
  have hDV (e : E3) (he : ‖e‖ = 1) : ‖fderiv ℝ V x e‖ ≤ A := by
    simpa only [he, mul_one] using (fderiv ℝ V x).le_of_opNorm_le hV.first e
  have hDW (e : E3) (he : ‖e‖ = 1) : ‖fderiv ℝ W x e‖ ≤ B := by
    simpa only [he, mul_one] using (fderiv ℝ W x).le_of_opNorm_le hW.first e
  refine ⟨hV.smooth.inner ℝ hW.smooth, ?_, ?_, ?_⟩
  · exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul hV.value hW.value (norm_nonneg _) hA).trans (by nlinarith))
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    rw [((hV.smooth.differentiableAt (by norm_num)).hasFDerivAt.inner ℝ
      (hW.smooth.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    change ‖⟪V x, fderiv ℝ W x e⟫ + ⟪fderiv ℝ V x e, W x⟫‖ ≤ _
    calc
      _ ≤ ‖V x‖ * ‖fderiv ℝ W x e‖ + ‖fderiv ℝ V x e‖ * ‖W x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ A * B + A * B := by
        gcongr
        · exact hV.value
        · exact hDW e he
        · exact hDV e he
        · exact hW.value
      _ ≤ _ := by nlinarith
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro e he
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro f hf
    have hDDV : ‖fderiv ℝ (fderiv ℝ V) x e f‖ ≤ A := by
      simpa only [mul_one] using
        (fderiv ℝ (fderiv ℝ V) x).le_of_opNorm₂_le_of_le hV.second he.le hf.le
    have hDDW : ‖fderiv ℝ (fderiv ℝ W) x e f‖ ≤ B := by
      simpa only [mul_one] using
        (fderiv ℝ (fderiv ℝ W) x).le_of_opNorm₂_le_of_le hW.second he.le hf.le
    rw [levelGradDecay_fderiv_two_inner hV.smooth hW.smooth]
    calc
      _ ≤ ‖⟪V x, fderiv ℝ (fderiv ℝ W) x e f⟫‖ +
          ‖⟪fderiv ℝ V x e, fderiv ℝ W x f⟫‖ +
          ‖⟪fderiv ℝ V x f, fderiv ℝ W x e⟫‖ +
          ‖⟪fderiv ℝ (fderiv ℝ V) x e f, W x⟫‖ :=
        (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
      _ ≤ A * B + A * B + A * B + A * B := by
        gcongr
        · exact (norm_inner_le_norm _ _).trans (by gcongr; exact hV.value)
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul (hDV e he) (hDW f hf) (norm_nonneg _) hA)
        · exact (norm_inner_le_norm _ _).trans
            (mul_le_mul (hDV f hf) (hDW e he) (norm_nonneg _) hA)
        · exact (norm_inner_le_norm _ _).trans (by gcongr; exact hW.value)
      _ = _ := by ring

set_option maxSynthPendingDepth 8 in
-- Compactness is applied also to the second derivative, a nested map space.
/-- Compactness supplies simultaneous bounds for two derivatives on the unit sphere. -/
theorem levelGradDecay_sphere_jet_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F}
    (hf : ∀ x : E3, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : E3, ‖θ‖ = 1 → levelGradDecay_JetBound f θ B := by
  have hθ0 : ∀ θ ∈ sphere (0 : E3) 1, θ ≠ 0 := by
    intro θ hθ he
    simp [he] at hθ
  have hc : ContinuousOn f (sphere 0 1) := fun θ hθ =>
    (hf θ (hθ0 θ hθ)).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fderiv ℝ f) (sphere 0 1) := fun θ hθ =>
    ((hf θ (hθ0 θ hθ)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hDD : ContinuousOn (fderiv ℝ (fderiv ℝ f)) (sphere 0 1) := fun θ hθ =>
    (((hf θ (hθ0 θ hθ)).fderiv_right (m := 1) (by simp)).fderiv_right
      (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hb₀⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn hc
  obtain ⟨B₁, hb₁⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn hD
  obtain ⟨B₂, hb₂⟩ := (isCompact_sphere (0 : E3) 1).exists_bound_of_continuousOn hDD
  refine ⟨max 1 (max B₀ (max B₁ B₂)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro θ hθ
  have hm : θ ∈ sphere (0 : E3) 1 := by simpa only [mem_sphere, dist_zero_right] using hθ
  refine ⟨(hf θ (hθ0 θ hm)).of_le (by simp), (hb₀ θ hm).trans ?_,
    (hb₁ θ hm).trans ?_, (hb₂ θ hm).trans ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

set_option maxSynthPendingDepth 8 in
-- Differentiating a derivative requires nested continuous-linear-map instances.
/-- The second total derivative transforms quadratically under dilation. -/
theorem levelGradDecay_fderiv_two_comp_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E3 → F) (c : ℝ) (x : E3) :
    fderiv ℝ (fderiv ℝ (fun y => f (c • y))) x =
      c ^ 2 • fderiv ℝ (fderiv ℝ f) (c • x) := by
  have he : fderiv ℝ (fun y => f (c • y)) =
      c • (fun y => fderiv ℝ f (c • y)) := by
    funext y
    exact fderiv_comp_smul c
  rw [he, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul, pow_two]

set_option maxSynthPendingDepth 8 in
-- The third scalar derivative and second vector derivative are nested maps.
/-- Rescaling the harmonic gradient remainder makes its first two derivatives
the same order as its value. -/
theorem levelGradDecay_rescaled_gradient_jet {W : E3 → ℝ} {θ : E3} {r M : ℝ}
    (hr : 0 < r) (hW : ContDiffAt ℝ 3 W (r • θ))
    (h₁ : ‖fderiv ℝ W (r • θ)‖ ≤ M / r ^ 5)
    (h₂ : ‖fderiv ℝ (fderiv ℝ W) (r • θ)‖ ≤ M / r ^ 6)
    (h₃ : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ W)) (r • θ)‖ ≤ M / r ^ 7) :
    levelGradDecay_JetBound (fun y => gradient W (r • y)) θ (M * r⁻¹ ^ 5) := by
  have hG : ContDiffAt ℝ 2 (gradient W) (r • θ) :=
    (toDual ℝ E3).symm.contDiff.contDiffAt.comp _ (hW.fderiv_right (by norm_num))
  refine ⟨hG.comp θ (contDiffAt_id.const_smul r), ?_, ?_, ?_⟩
  · simpa only [gradient, (toDual ℝ E3).symm.norm_map, inv_pow, div_eq_mul_inv] using h₁
  · rw [fderiv_comp_smul, norm_smul, Real.norm_of_nonneg hr.le]
    calc
      _ ≤ r * (M / r ^ 6) := mul_le_mul_of_nonneg_left
        ((levelGrad_norm_fderiv_gradient_le W _).trans h₂) hr.le
      _ = _ := by field_simp
  · rw [levelGradDecay_fderiv_two_comp_smul, norm_smul,
      Real.norm_of_nonneg (sq_nonneg r), levelAreaSecond_norm_fderiv_two_gradient,
      levelGradSecond_norm_iteratedFDeriv_three]
    calc
      _ ≤ r ^ 2 * (M / r ^ 7) := mul_le_mul_of_nonneg_left h₃ (sq_nonneg r)
      _ = _ := by field_simp

/-- A positive inward radial component gives an exact quadratic norm correction. -/
theorem levelGradDecay_norm_radial_identity {g n : E3} {a : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hg : ⟪g, n⟫ = -a) :
    ‖g‖ = a * Real.sqrt (1 + ‖a⁻¹ • (g + a • n)‖ ^ 2) := by
  have h := levelAreaSecond_norm_quotient hn (by rw [hg]; exact neg_ne_zero.mpr ha.ne')
  rw [hg, abs_neg, abs_of_pos ha, inv_neg, neg_smul, norm_neg, neg_smul,
    sub_neg_eq_add] at h
  exact (div_eq_iff ha.ne').mp h |>.trans (mul_comm _ _)

/-- The square-root correction has quadratic jet size. -/
theorem levelGradDecay_sqrt_jet {V : E3 → E3} {x : E3} {B ε : ℝ}
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hV : levelGradDecay_JetBound V x (B * ε ^ 2)) :
    levelGradDecay_JetBound (fun y => Real.sqrt (1 + ‖V y‖ ^ 2) - 1) x
      ((2 * B ^ 2 + B ^ 4) * ε ^ 4) := by
  obtain ⟨h₀, h₁, h₂⟩ := levelAreaSecond_sqrt_norm_sq_bounds hV.smooth
  have hpow : ε ^ 8 ≤ ε ^ 4 := pow_le_pow_of_le_one hε hε1 (by norm_num)
  have hB4 : 0 ≤ B ^ 4 := by positivity
  refine ⟨((contDiffAt_const.add (hV.smooth.norm_sq (𝕜 := ℝ))).sqrt
    (by positivity)).sub contDiffAt_const, h₀.trans ?_, h₁.trans ?_, h₂.trans ?_⟩
  · calc
      _ ≤ (B * ε ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hV.value 2
      _ ≤ _ := by nlinarith [mul_nonneg hB4 (pow_nonneg hε 4)]
  · calc
      _ ≤ (B * ε ^ 2) * (B * ε ^ 2) :=
        mul_le_mul hV.value hV.first (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hB4 (pow_nonneg hε 4)]
  · calc
      _ ≤ (B * ε ^ 2) ^ 2 + (B * ε ^ 2) * (B * ε ^ 2) +
          (B * ε ^ 2) ^ 2 * (B * ε ^ 2) ^ 2 := by
        gcongr
        · exact hV.first
        · exact hV.value
        · exact hV.second
        · exact hV.value
        · exact hV.first
      _ = 2 * B ^ 2 * ε ^ 4 + B ^ 4 * ε ^ 8 := by ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow hB4]

set_option maxHeartbeats 600000 in
-- The rescaled nonlinear estimate combines the product and quotient jet bounds.
/-- Uniform second-order control of the nonlinear norm error after rescaling.
The radial part of `F` is exactly `-q`; the remaining perturbation has order five. -/
theorem levelGradDecay_norm_remainder_jet {C B M : ℝ}
    (hC : 0 < C) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (ε : ℝ) (p q : E3 → ℝ) (n F w : E3 → E3) (θ : E3),
      0 < ε → ε ≤ 1 →
      levelGradDecay_JetBound p θ B → levelGradDecay_JetBound q θ B →
      levelGradDecay_JetBound n θ B → levelGradDecay_JetBound F θ B →
      levelGradDecay_JetBound w θ (M * ε ^ 5) → p θ = C →
      (∀ᶠ y in 𝓝 θ, ‖n y‖ = 1 ∧ ⟪F y, n y⟫ = -q y) →
      (B + 4 * M * B) * ε ^ 2 ≤ C / 2 →
      levelGradDecay_JetBound
        (fun y => ‖-(ε ^ 2 * p y) • n y + ε ^ 4 • F y + w y‖ -
          ε ^ 2 * p y - ε ^ 4 * q y) θ (H * ε ^ 5) := by
  let E := 4 * M * B
  let D₀ := 2 * B + E
  let D := D₀ + 2 / C
  let J := B + 4 * B ^ 2 + M + 4 * E * B
  let L := J * (D + 3 * D ^ 3 + 2 * D ^ 5)
  let H := E + 4 * D * (2 * L ^ 2 + L ^ 4)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨H, by dsimp [H]; positivity, ?_⟩
  intro ε p q n F w θ hε hε1 hp hq hn hF hw hpC hmodel hsmall
  have h52 : ε ^ 5 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h42 : ε ^ 4 ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h54 : ε ^ 5 ≤ ε ^ 4 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have h65 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  let b : E3 → ℝ := fun y => ⟪w y, n y⟫
  have hb : levelGradDecay_JetBound b θ (E * ε ^ 5) := by
    convert levelGradDecay_jet_inner hw hn using 1
    dsimp only [E]
    ring
  have hnb : levelGradDecay_JetBound (fun y => -b y) θ (E * ε ^ 5) := by
    simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
      levelGradDecay_jet_const_smul hb (-1)
  have hp' : levelGradDecay_JetBound (fun y => ε ^ 2 * p y) θ (B * ε ^ 2) := by
    have h := levelGradDecay_jet_const_smul hp (ε ^ 2)
    rw [abs_of_nonneg (sq_nonneg ε)] at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hq' : levelGradDecay_JetBound (fun y => ε ^ 4 * q y) θ (B * ε ^ 4) := by
    have h := levelGradDecay_jet_const_smul hq (ε ^ 4)
    rw [abs_of_nonneg (pow_nonneg hε.le 4)] at h
    simpa only [smul_eq_mul, mul_comm] using h
  let a : E3 → ℝ := fun y => ε ^ 2 * p y + ε ^ 4 * q y + -b y
  have ha₀ : levelGradDecay_JetBound a θ (D₀ * ε ^ 2) := by
    apply levelGradDecay_jet_mono (levelGradDecay_jet_add
      (levelGradDecay_jet_add hp' hq') hnb)
    calc
      _ ≤ B * ε ^ 2 + B * ε ^ 2 + E * ε ^ 2 := by gcongr
      _ = _ := by dsimp [D₀]; ring
  have ha : levelGradDecay_JetBound a θ (D * ε ^ 2) :=
    levelGradDecay_jet_mono ha₀ (mul_le_mul_of_nonneg_right
      (by dsimp only [D]; exact le_add_of_nonneg_right (by positivity)) (sq_nonneg ε))
  have halower : C * ε ^ 2 / 2 ≤ a θ := by
    have hqlo := (abs_le.mp (show |q θ| ≤ B from hq.value)).1
    have hbhi := (abs_le.mp (show |b θ| ≤ E * ε ^ 5 from hb.value)).2
    have he54 := mul_le_mul_of_nonneg_left h54 hE
    have hqe := mul_le_mul_of_nonneg_left hqlo (pow_nonneg hε.le 4)
    have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ε)
    change (B + E) * ε ^ 2 * ε ^ 2 ≤ C / 2 * ε ^ 2 at hs
    dsimp only [a]
    rw [hpC]
    nlinarith only [hbhi, he54, hqe, hs]
  have hapos : 0 < a θ := (by positivity : 0 < C * ε ^ 2 / 2).trans_le halower
  have hi : |(a θ)⁻¹| ≤ D / ε ^ 2 := by
    rw [abs_of_pos (inv_pos.mpr hapos)]
    calc
      _ ≤ (C * ε ^ 2 / 2)⁻¹ := (inv_le_inv₀ hapos (by positivity)).mpr halower
      _ = (2 / C) / ε ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [D]; linarith) (sq_nonneg ε)
  let V : E3 → E3 := fun y =>
    ε ^ 4 • (F y + q y • n y) + (w y + (-b y) • n y)
  have hV : levelGradDecay_JetBound V θ (J * ε ^ 4) := by
    have hqn := levelGradDecay_jet_smul hq hn
    have hFn := levelGradDecay_jet_add hF hqn
    have hFsc := levelGradDecay_jet_const_smul hFn (ε ^ 4)
    have hbn := levelGradDecay_jet_smul hnb hn
    have hsum := levelGradDecay_jet_add hFsc (levelGradDecay_jet_add hw hbn)
    apply levelGradDecay_jet_mono hsum
    rw [abs_of_nonneg (pow_nonneg hε.le 4)]
    calc
      _ = (B + 4 * B ^ 2) * ε ^ 4 + (M + 4 * E * B) * ε ^ 5 := by ring
      _ ≤ (B + 4 * B ^ 2) * ε ^ 4 + (M + 4 * E * B) * ε ^ 4 := by gcongr
      _ = _ := by dsimp [J]; ring
  let T : E3 → E3 := fun y => (a y)⁻¹ • V y
  have hT : levelGradDecay_JetBound T θ (L * ε ^ 2) := by
    obtain ⟨hv, hd, hdd⟩ := levelAreaSecond_quotient_bounds_small hD hJ hε
      ha.smooth hV.smooth hapos.ne' hi ha.first ha.second hV.value hV.first hV.second
    exact ⟨(ha.smooth.inv hapos.ne').smul hV.smooth, hv, hd, hdd⟩
  have hsqrt := levelGradDecay_sqrt_jet hL hε.le hε1 hT
  have hprod := levelGradDecay_jet_mul ha hsqrt
  have hsum := levelGradDecay_jet_add hnb hprod
  have hbound : levelGradDecay_JetBound
      (fun y => -b y + a y * (Real.sqrt (1 + ‖T y‖ ^ 2) - 1)) θ (H * ε ^ 5) := by
    apply levelGradDecay_jet_mono hsum
    calc
      _ = E * ε ^ 5 + (4 * D * (2 * L ^ 2 + L ^ 4)) * ε ^ 6 := by
        ring_nf (config := { zetaDelta := false })
      _ ≤ E * ε ^ 5 + (4 * D * (2 * L ^ 2 + L ^ 4)) * ε ^ 5 := by gcongr
      _ = _ := by dsimp only [H]; ring_nf (config := { zetaDelta := false })
  apply levelGradDecay_jet_congr hbound
  filter_upwards [hmodel, ha.smooth.continuousAt.eventually (lt_mem_nhds hapos)]
    with y hy hay
  let g := -(ε ^ 2 * p y) • n y + ε ^ 4 • F y + w y
  have hgn : ⟪g, n y⟫ = -a y := by
    dsimp [g, a, b]
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hy.1, hy.2]
    ring
  have hgV : g + a y • n y = V y := by
    dsimp [g, a, V]
    module
  have he := levelGradDecay_norm_radial_identity hy.1 hay hgn
  rw [hgV] at he
  change ‖g‖ - ε ^ 2 * p y - ε ^ 4 * q y = _
  rw [he]
  dsimp [T, a]
  ring

/-- The gradient-length error under dilation, using the homogeneous monopole and
quadrupole fields and the rescaled gradient of the potential remainder. -/
theorem levelGradDecay_rescaled_identity {U W Q : E3 → ℝ} {C r : ℝ} {y : E3}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hU : U = fun x => (C / ‖x‖ + farQuadrupole Q x) + W x)
    (hr : 0 < r) (hy : y ≠ 0) (hW : DifferentiableAt ℝ W (r • y)) :
    gradNorm U (r • y) - C * ‖r • y‖⁻¹ ^ 2 - 3 * Q (r • y) * ‖r • y‖⁻¹ ^ 6 =
      ‖-(r⁻¹ ^ 2 * (C * ‖y‖⁻¹ ^ 2)) • (‖y‖⁻¹ • y) +
        r⁻¹ ^ 4 • gradient (farQuadrupole Q) y + gradient W (r • y)‖ -
          r⁻¹ ^ 2 * (C * ‖y‖⁻¹ ^ 2) - r⁻¹ ^ 4 * (3 * Q y * ‖y‖⁻¹ ^ 6) := by
  have hx := smul_ne_zero hr.ne' hy
  have hm := (contDiffAt_monopole C hx).differentiableAt (by simp)
  have hq := (contDiffAt_farQuadrupole hQ hx).differentiableAt (by simp)
  have hmq : DifferentiableAt ℝ
      (fun x => C / ‖x‖ + farQuadrupole Q x) (r • y) := hm.add hq
  have hg : gradient U (r • y) =
      -(r⁻¹ ^ 2 * (C * ‖y‖⁻¹ ^ 2)) • (‖y‖⁻¹ • y) +
        r⁻¹ ^ 4 • gradient (farQuadrupole Q) y + gradient W (r • y) := by
    rw [hU, levelGrad_gradient_add hmq hW, levelGrad_gradient_add hm hq,
      gradient_monopole C hx, levelGrad_gradient_farQuadrupole_smul hQh hr,
      norm_smul, Real.norm_of_nonneg hr.le, smul_smul, smul_smul, inv_pow]
    simp only [inv_pow]
    congr 2
    field_simp
  dsimp only [gradNorm]
  rw [hg, norm_smul, Real.norm_of_nonneg hr.le, hQh]
  field_simp

set_option maxSynthPendingDepth 8 in
-- The input includes the third scalar derivative.
set_option maxHeartbeats 500000 in
-- Uniform rescaling uses four compact-sphere bounds and the nonlinear jet estimate.
/-- First and second spatial decay for the nonlinear gradient-length error.
Only three derivatives of the potential remainder are used. -/
theorem levelGradDecay_far_derivatives {U W Q : E3 → ℝ} {C R M : ℝ}
    (hC : 0 < C) (hM : 0 ≤ M)
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    (hQh : ∀ (c : ℝ) (x : E3), Q (c • x) = c ^ 2 * Q x)
    (hU : U = fun x => (C / ‖x‖ + farQuadrupole Q x) + W x)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W {x | R < ‖x‖})
    (hWd : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ W x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ W) x‖ ≤ M / ‖x‖ ^ 6 ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ W)) x‖ ≤ M / ‖x‖ ^ 7) :
    ∃ R' H : ℝ, R < R' ∧ 1 ≤ R' ∧ 0 ≤ H ∧ ∀ x : E3, R' ≤ ‖x‖ →
      ‖fderiv ℝ (fun y => gradNorm U y - C * ‖y‖⁻¹ ^ 2 -
        3 * Q y * ‖y‖⁻¹ ^ 6) x‖ ≤ H / ‖x‖ ^ 6 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => gradNorm U y - C * ‖y‖⁻¹ ^ 2 -
        3 * Q y * ‖y‖⁻¹ ^ 6)) x‖ ≤ H / ‖x‖ ^ 7 := by
  let p : E3 → ℝ := fun y => C * ‖y‖⁻¹ ^ 2
  let q : E3 → ℝ := fun y => 3 * Q y * ‖y‖⁻¹ ^ 6
  let n : E3 → E3 := fun y => ‖y‖⁻¹ • y
  let F : E3 → E3 := gradient (farQuadrupole Q)
  have hp : ∀ y : E3, y ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) p y := by
    intro y hy
    exact contDiffAt_const.mul
      (((contDiffAt_id.norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).pow 2)
  have hq : ∀ y : E3, y ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q y := by
    intro y hy
    exact (contDiffAt_const.mul hQ.contDiffAt).mul
      (((contDiffAt_id.norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).pow 6)
  have hn : ∀ y : E3, y ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) n y :=
    fun _ hy => levelRadius_normalize_contDiffAt hy
  have hF : ∀ y : E3, y ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) F y := by
    intro y hy
    exact (toDual ℝ E3).symm.contDiff.contDiffAt.comp y
      ((contDiffAt_farQuadrupole hQ hy).fderiv_right (by simp))
  obtain ⟨Bp, hBp, hpb⟩ := levelGradDecay_sphere_jet_bound hp
  obtain ⟨Bq, hBq, hqb⟩ := levelGradDecay_sphere_jet_bound hq
  obtain ⟨Bn, hBn, hnb⟩ := levelGradDecay_sphere_jet_bound hn
  obtain ⟨Bf, hBf, hfb⟩ := levelGradDecay_sphere_jet_bound hF
  let B := Bp + Bq + Bn + Bf
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨H, hH, hHb⟩ := levelGradDecay_norm_remainder_jet hC hB hM
  have hlim : Tendsto (fun s : ℝ => (B + 4 * M * B) / s ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨R', hR', hsmall⟩ := ((eventually_ge_atTop (max (R + 1) 1)).and
    (hlim.eventually (gt_mem_nhds (by positivity : 0 < C / 2)))).exists
  have hRR : R < R' := by have := (le_max_left _ _).trans hR'; linarith
  have hR1 : 1 ≤ R' := (le_max_right _ _).trans hR'
  refine ⟨R', H, hRR, hR1, hH, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := zero_lt_one.trans_le (hR1.trans hx)
  have hx0 : x ≠ 0 := norm_pos_iff.mp hr
  let θ := ‖x‖⁻¹ • x
  have hθ : ‖θ‖ = 1 := by simp [θ, norm_smul, hr.ne']
  have hθ0 : θ ≠ 0 := by rintro he; simp [he] at hθ
  have hxθ : ‖x‖ • θ = x := by simp [θ, smul_smul, hr.ne']
  let w : E3 → E3 := fun y => gradient W (‖x‖ • y)
  have hxR : R < ‖x‖ := hRR.trans_le hx
  have hWc : ContDiffAt ℝ 3 W (‖x‖ • θ) := by
    rw [hxθ]
    exact (hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hxR)).of_le
      (by simp)
  obtain ⟨hW₁, hW₂, hW₃⟩ := hWd x hxR.le
  have hw : levelGradDecay_JetBound w θ (M * ‖x‖⁻¹ ^ 5) := by
    apply levelGradDecay_rescaled_gradient_jet hr hWc
    · simpa only [hxθ] using hW₁
    · simpa only [hxθ] using hW₂
    · simpa only [hxθ] using hW₃
  have hsmall' : (B + 4 * M * B) * ‖x‖⁻¹ ^ 2 ≤ C / 2 := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (zero_le_one.trans hR1) hx 2)).trans hsmall.le
  have hmodel : ∀ᶠ y in 𝓝 θ, ‖n y‖ = 1 ∧ ⟪F y, n y⟫ = -q y := by
    filter_upwards [isOpen_ne.mem_nhds hθ0] with y hy
    refine ⟨by simp [n, norm_smul, norm_ne_zero_iff.mpr hy], ?_⟩
    dsimp [F, n, q]
    rw [inner_smul_right, real_inner_comm, inner_gradient_farQuadrupole hQ hQh hy]
    dsimp [farQuadrupole]
    field_simp
  have hjet := hHb ‖x‖⁻¹ p q n F w θ (inv_pos.mpr hr)
    ((inv_le_one₀ hr).mpr (hR1.trans hx))
    (levelGradDecay_jet_mono (hpb θ hθ) (by dsimp [B]; linarith))
    (levelGradDecay_jet_mono (hqb θ hθ) (by dsimp [B]; linarith))
    (levelGradDecay_jet_mono (hnb θ hθ) (by dsimp [B]; linarith))
    (levelGradDecay_jet_mono (hfb θ hθ) (by dsimp [B]; linarith))
    hw (by simp [p, hθ]) hmodel hsmall'
  let S : E3 → ℝ := fun y => gradNorm U y - C * ‖y‖⁻¹ ^ 2 - 3 * Q y * ‖y‖⁻¹ ^ 6
  have heq : (fun y => S (‖x‖ • y)) =ᶠ[𝓝 θ]
      (fun y => ‖-(‖x‖⁻¹ ^ 2 * p y) • n y + ‖x‖⁻¹ ^ 4 • F y + w y‖ -
        ‖x‖⁻¹ ^ 2 * p y - ‖x‖⁻¹ ^ 4 * q y) := by
    have hext : ∀ᶠ y in 𝓝 θ, R < ‖‖x‖ • y‖ :=
      ((continuous_const_smul ‖x‖).norm.continuousAt).eventually
        (lt_mem_nhds (by simpa only [hxθ] using hxR))
    filter_upwards [isOpen_ne.mem_nhds hθ0, hext] with y hy hyR
    have hWy := hW.contDiffAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hyR)
    exact levelGradDecay_rescaled_identity hQ hQh hU hr hy (hWy.differentiableAt (by simp))
  have hSjet := levelGradDecay_jet_congr hjet heq
  have h₁ := hSjet.first
  have h₂ := hSjet.second
  rw [fderiv_comp_smul, norm_smul, Real.norm_of_nonneg hr.le, hxθ] at h₁
  rw [levelGradDecay_fderiv_two_comp_smul, norm_smul,
    Real.norm_of_nonneg (sq_nonneg ‖x‖), hxθ] at h₂
  constructor
  · calc
      ‖fderiv ℝ S x‖ ≤ (H * ‖x‖⁻¹ ^ 5) / ‖x‖ := (le_div_iff₀ hr).mpr (by
        simpa only [mul_comm] using h₁)
      _ = _ := by field_simp
  · calc
      ‖fderiv ℝ (fderiv ℝ S) x‖ ≤ (H * ‖x‖⁻¹ ^ 5) / ‖x‖ ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using h₂)
      _ = _ := by field_simp

set_option maxSynthPendingDepth 8 in
-- The third derivative hypothesis is a norm on three nested linear maps.
/-- Smoothness and the two required decay estimates for the actual translated
spatial gradient-length remainder, keeping the supplied Kelvin extension fixed. -/
theorem levelGradDecay_spatial_derivatives {u v : E3 → ℝ} {R M : ℝ}
    (hC : 0 < v 0) (hM : 0 ≤ M)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTranslatedRemainder u v) {x | R < ‖x‖})
    (hWd : ∀ x : E3, R ≤ ‖x‖ →
      ‖fderiv ℝ (kelvinTranslatedRemainder u v) x‖ ≤ M / ‖x‖ ^ 5 ∧
      ‖fderiv ℝ (fderiv ℝ (kelvinTranslatedRemainder u v)) x‖ ≤ M / ‖x‖ ^ 6 ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (kelvinTranslatedRemainder u v))) x‖ ≤
        M / ‖x‖ ^ 7) :
    ∃ R' H : ℝ, R < R' ∧ 1 ≤ R' ∧ 0 ≤ H ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (levelGradSecond_spatialRemainder u v) {x | R' < ‖x‖} ∧
      ∀ x : E3, R' ≤ ‖x‖ →
        ‖fderiv ℝ (levelGradSecond_spatialRemainder u v) x‖ ≤ H / ‖x‖ ^ 6 ∧
        ‖fderiv ℝ (fderiv ℝ (levelGradSecond_spatialRemainder u v)) x‖ ≤ H / ‖x‖ ^ 7 := by
  let U : E3 → ℝ := fun y => u (y + (v 0)⁻¹ • gradient v 0)
  have hU : U = fun y =>
      (v 0 / ‖y‖ + farQuadrupole (kelvinTranslatedQuadrupole v) y) +
        kelvinTranslatedRemainder u v y := by
    funext y
    dsimp [U, farQuadrupole, kelvinTranslatedRemainder]
    ring
  obtain ⟨R₁, H, hR₁, hR₁1, hH, hD⟩ := levelGradDecay_far_derivatives hC hM
    (translated_quadrupole_contDiff v) (kelvinTranslatedQuadrupole_smul v) hU hW hWd
  have hGN : gradNorm U = fun y => gradNorm u (y + (v 0)⁻¹ • gradient v 0) := by
    funext y
    simp only [gradNorm, U, gradient, fderiv_comp_add_right]
  change ∀ x : E3, R₁ ≤ ‖x‖ →
    ‖fderiv ℝ (fun y => gradNorm U y - v 0 * ‖y‖⁻¹ ^ 2 -
      3 * kelvinTranslatedQuadrupole v y * ‖y‖⁻¹ ^ 6) x‖ ≤ H / ‖x‖ ^ 6 ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => gradNorm U y - v 0 * ‖y‖⁻¹ ^ 2 -
      3 * kelvinTranslatedQuadrupole v y * ‖y‖⁻¹ ^ 6)) x‖ ≤ H / ‖x‖ ^ 7 at hD
  rw [hGN] at hD
  obtain ⟨R₂, _, _, hs⟩ := levelGradDecay_spatial_smooth hC hW
    (fun x hx => (hWd x hx).1)
  refine ⟨max R₁ R₂, H, hR₁.trans_le (le_max_left _ _),
    hR₁1.trans (le_max_left _ _), hH,
    hs.mono (fun x hx => by
      exact (le_max_right R₁ R₂).trans_lt hx), ?_⟩
  intro x hx
  exact hD x ((le_max_left _ _).trans hx)

/-- Capacitary spatial gradient-length remainder estimates through second order.
The Kelvin extension is exactly the one used for the translated potential remainder. -/
theorem levelGradDecay_capacitary_spatial_derivatives
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ (v : E3 → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ 0 < v 0 ∧
      ∃ R M : ℝ, 1 ≤ R ∧ 0 ≤ M ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (levelGradSecond_spatialRemainder u v) {x | R < ‖x‖} ∧
        ∀ x : E3, R ≤ ‖x‖ →
          ‖fderiv ℝ (levelGradSecond_spatialRemainder u v) x‖ ≤ M / ‖x‖ ^ 6 ∧
          ‖fderiv ℝ (fderiv ℝ (levelGradSecond_spatialRemainder u v)) x‖ ≤ M / ‖x‖ ^ 7 := by
  obtain ⟨v, r, hr, hv, he, hv0, R, M, _, hM, hW, hD⟩ :=
    levelGradSecond_capacitary_translated_remainder_derivatives
      hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨R', H, _, hR', hH, hs, hDb⟩ := levelGradDecay_spatial_derivatives hv0 hM hW
    (fun x hx => (hD x hx).2)
  exact ⟨v, r, hr, hv, he, hv0, R', H, hR', hH, hs, hDb⟩

end LiquidDrop.CapacitaryK
