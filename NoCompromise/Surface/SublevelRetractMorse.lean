import NoCompromise.Surface.SublevelRetract

/-!
# Closed sublevel retractions for Morse functions

The gradient-height bound at a nondegenerate critical point follows from a
quadratic height bound and a linear lower bound for the surface gradient.
-/

noncomputable section

open Set Filter Function InnerProductSpace
open scoped Topology Gradient

namespace LiquidDrop

/-- The height changes at most quadratically along the surface near a critical point. -/
theorem exists_surface_height_quadratic_bound {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) :
    ∃ C > 0, ∀ᶠ x in 𝓝[S] p, |h x - h p| ≤ C * ‖x - p‖ ^ 2 := by
  obtain ⟨U, φ, hU, hpU, hφ, hzero, hreg⟩ := hS p hp.1
  have hT := tangentPlane_eq hU hpU (hφ.of_le (by simp)).contDiffAt
    hzero hp.1 (hreg p ⟨hp.1, hpU⟩)
  have hgrad : gradient h p ∈ (ℝ ∙ gradient φ p) := by
    rw [← Submodule.orthogonal_orthogonal (ℝ ∙ gradient φ p)]
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro X hX
    rw [inner_gradient_left]
    exact hp.2 X (hT ▸ hX)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgrad
  let ψ : E₃ → ℝ := fun x => h x - c * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hh.sub (contDiff_const.mul hφ)
  have hdψ : fderiv ℝ ψ p = 0 := by
    ext X
    rw [show fderiv ℝ ψ p = fderiv ℝ h p - c • fderiv ℝ φ p from
      (hh.differentiable (by simp) p).hasFDerivAt.sub
        ((hφ.differentiable (by simp) p).hasFDerivAt.const_mul c) |>.fderiv]
    simp only [sub_apply, smul_apply, zero_apply, smul_eq_mul]
    rw [← inner_gradient_left, ← inner_gradient_left, ← hc, real_inner_smul_left]
    ring
  obtain ⟨K, V, hV, hLip⟩ :=
    (hψ.fderiv_right (m := 1) (by simp)).contDiffAt.exists_lipschitzOnWith (x := p)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hpV : p ∈ V := mem_of_mem_nhds hV
  have hψbound {x : E₃} (hx : x ∈ Metric.ball p r) :
      |ψ x - ψ p| ≤ (K : ℝ) * ‖x - p‖ ^ 2 := by
    have hball : Metric.closedBall p ‖x - p‖ ⊆ V := by
      intro z hz
      apply hrV
      exact lt_of_le_of_lt hz (by simpa [Metric.mem_ball, dist_eq_norm] using hx)
    have hb (z : E₃) (hz : z ∈ Metric.closedBall p ‖x - p‖) :
        ‖fderiv ℝ ψ z‖ ≤ (K : ℝ) * ‖x - p‖ := by
      have hL := hLip.dist_le_mul z (hball hz) p hpV
      rw [hdψ, dist_zero_right, dist_eq_norm] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz) K.coe_nonneg)
    have hmv := (convex_closedBall p ‖x - p‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hψ.differentiable (by simp) z) hb
      (Metric.mem_closedBall_self (norm_nonneg _))
      (show x ∈ Metric.closedBall p ‖x - p‖ by simp [dist_eq_norm])
    simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hmv
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hpU),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hr)] with x hx hxU hxr
  have hxφ : φ x = 0 := (hzero ▸ (show x ∈ S ∩ U from ⟨hx, hxU⟩)).2
  have hpφ : φ p = 0 := (hzero ▸ (show p ∈ S ∩ U from ⟨hp.1, hpU⟩)).2
  have hb := hψbound hxr
  simp only [ψ, hxφ, hpφ, mul_zero, sub_zero] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

private lemma sublevel_surfaceGradient_differentiableAt {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {p : E₃} (hp : p ∈ S) : DifferentiableAt ℝ (surfaceGradient n h) p := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ h) p :=
    (hh.fderiv_right (m := 1) (by simp)).differentiable (by simp) p
  have h1 : DifferentiableAt ℝ (gradient h) p :=
    (toDual ℝ E₃).symm.toContinuousLinearEquiv.differentiableAt.comp p hfd
  have h2 : DifferentiableAt ℝ n p := (hn.contDiffAt hp).differentiableAt (by simp)
  exact h1.sub ((h2.inner ℝ h1).smul h2)

/-- Near a nondegenerate critical point the surface gradient controls ambient distance. -/
theorem exists_surface_gradient_dist_bound {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    ∃ C > 0, ∀ᶠ x in 𝓝[S] p, ‖x - p‖ ≤ C * ‖surfaceGradient n h x‖ := by
  have hlocal : ∃ C > 0, ∃ r > 0, ∀ x ∈ S, ‖x - p‖ < r →
      ‖x - p‖ ≤ C * ‖surfaceGradient n h x‖ := by
    by_contra! hbad
    have hchoice (k : ℕ) : ∃ x ∈ S, ‖x - p‖ < 1 / ((k : ℝ) + 1) ∧
        ((k : ℝ) + 1) * ‖surfaceGradient n h x‖ < ‖x - p‖ :=
      hbad ((k : ℝ) + 1) (by positivity) (1 / ((k : ℝ) + 1)) (by positivity)
    choose q hqS hqdist hqgrad using hchoice
    have hqne (k : ℕ) : q k ≠ p := by
      intro heq
      have := hqgrad k
      simp only [heq, sub_self, norm_zero] at this
      exact (not_lt_of_ge (by positivity)) this
    have hdpos (k : ℕ) : 0 < ‖q k - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hqne k))
    have hq : Tendsto q atTop (𝓝 p) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun k => dist_nonneg) (fun k => by
        simpa [dist_eq_norm] using (hqdist k).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hunit (k : ℕ) : ‖q k - p‖⁻¹ • (q k - p) ∈ Metric.sphere (0 : E₃) 1 := by
      simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        ne_of_gt (hdpos k)]
    obtain ⟨u, huunit, r, hr, hu⟩ := (isCompact_sphere (0 : E₃) 1).tendsto_subseq hunit
    have hqr : Tendsto (q ∘ r) atTop (𝓝 p) := hq.comp hr.tendsto_atTop
    have huT : u ∈ tangentPlane S p :=
      mem_tangentPlane_of_tendsto_normalized_secant hp.1 (fun k => hqS (r k)) hqr hu
    let g := surfaceGradient n h
    have hgp : g p = 0 := (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hp.1).mp hp
    have hgd : DifferentiableAt ℝ g p := sublevel_surfaceGradient_differentiableAt hn hh hp.1
    have hsmall : Tendsto (fun k => ‖q k - p‖⁻¹ * ‖g (q k)‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun k => by positivity) (fun k => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [← div_eq_inv_mul]
      apply (div_le_div_iff₀ (hdpos k) (by positivity : 0 < (k : ℝ) + 1)).mpr
      simpa [mul_comm] using (hqgrad k).le
    have hrem := (hasFDerivAt_iff_tendsto.mp hgd.hasFDerivAt).comp hq
    have hderzero : Tendsto (fun k => ‖fderiv ℝ g p (‖q k - p‖⁻¹ • (q k - p))‖)
        atTop (𝓝 0) := by
      apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        (show Tendsto (fun k =>
          ‖q k - p‖⁻¹ * ‖g (q k) - g p - fderiv ℝ g p (q k - p)‖ +
          ‖q k - p‖⁻¹ * ‖g (q k)‖) atTop (𝓝 0) from by
          simpa only [Function.comp_apply, add_zero] using hrem.add hsmall)
      rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        ← mul_add]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
      rw [hgp, sub_zero, norm_sub_rev]
      calc
        ‖fderiv ℝ g p (q k - p)‖ =
            ‖(fderiv ℝ g p (q k - p) - g (q k)) + g (q k)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hdu : fderiv ℝ g p u = 0 := by
      have hl := (((fderiv ℝ g p).continuous.tendsto u).comp hu).norm
      exact norm_eq_zero.mp (tendsto_nhds_unique hl (hderzero.comp hr.tendsto_atTop))
    have hzero := hnd ⟨u, huT⟩ (fun Y => by
      change surfaceHessian n h p u Y = 0
      rw [← inner_fderiv_surfaceGradient hS hn (hh.of_le (by simp)) hp.1 u Y Y.property,
        hdu, inner_zero_left])
    have hu0 : u = 0 := congrArg Subtype.val hzero
    simp [hu0] at huunit
  obtain ⟨C, hC, r, hr, hbound⟩ := hlocal
  refine ⟨C, hC, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hr)] with x hx hxr
  exact hbound x hx (by simpa [Metric.mem_ball, dist_eq_norm] using hxr)

/-- The local gradient-height bound at a nondegenerate critical point. -/
theorem exists_local_gradient_height_bound {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p)
    (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    ∃ C > 0, ∀ᶠ x in 𝓝[S] p, |h x - h p| ≤ C * ‖surfaceGradient n h x‖ ^ 2 := by
  obtain ⟨A, hA, hheight⟩ := exists_surface_height_quadratic_bound hS hh hp
  obtain ⟨B, hB, hgrad⟩ := exists_surface_gradient_dist_bound hS hn hh hp hnd
  refine ⟨A * B ^ 2, by positivity, ?_⟩
  filter_upwards [hheight, hgrad] with x hxheight hxgrad
  calc
    |h x - h p| ≤ A * ‖x - p‖ ^ 2 := hxheight
    _ ≤ A * (B * ‖surfaceGradient n h x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxgrad 2) hA.le
    _ = (A * B ^ 2) * ‖surfaceGradient n h x‖ ^ 2 := by ring

/-- On a compact Morse surface with no critical values in `(a,b]`, the height
above `a` is bounded by a constant times the square of the surface gradient. -/
theorem exists_gradient_height_bound {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmorse : IsSurfaceMorse S n h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ioc a b) :
    ∃ C > 0, ∀ x ∈ S, a < h x → h x ≤ b →
      h x - a ≤ C * ‖surfaceGradient n h x‖ ^ 2 := by
  classical
  let K := S ∩ h ⁻¹' Icc a b
  have hK : IsCompact K := hc.inter_right (isClosed_Icc.preimage hh.continuous)
  have hlocal (p : K) : ∃ C > 0, ∀ᶠ x in 𝓝[K] (p : E₃),
      h x - a ≤ C * ‖surfaceGradient n h x‖ ^ 2 := by
    by_cases hp : IsSurfaceCriticalPoint S h p
    · have hpa : h p = a := by
        have hnot := hreg p hp
        have hmem := p.property.2
        change a ≤ h p ∧ h p ≤ b at hmem
        by_contra hne
        exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
      obtain ⟨C, hC, hbound⟩ := exists_local_gradient_height_bound hS hn hh hp (hmorse p hp)
      refine ⟨C, hC, ?_⟩
      filter_upwards [hbound.filter_mono (nhdsWithin_mono (p : E₃) inter_subset_left)] with x hx
      rw [hpa] at hx
      exact (le_abs_self _).trans hx
    · have hgp : 0 < ‖surfaceGradient n h p‖ := by
        apply norm_pos_iff.mpr
        exact fun hz => hp ((isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero
          hS hn p.property.1).mpr hz)
      let m := ‖surfaceGradient n h p‖ / 2
      have hm : 0 < m := by dsimp [m]; positivity
      have hnear : ∀ᶠ x in 𝓝 (p : E₃), m < ‖surfaceGradient n h x‖ :=
        (sublevel_surfaceGradient_differentiableAt hn hh p.property.1).continuousAt.norm
          |>.eventually (lt_mem_nhds (show m < ‖surfaceGradient n h (p : E₃)‖ from by
            dsimp [m]
            linarith))
      refine ⟨(b - a) / m ^ 2, by positivity, ?_⟩
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxK
      calc
        h x - a ≤ b - a := sub_le_sub_right hxK.2.2 a
        _ = ((b - a) / m ^ 2) * m ^ 2 := by field_simp
        _ ≤ ((b - a) / m ^ 2) * ‖surfaceGradient n h x‖ ^ 2 := by
          gcongr
  choose C hC hbound using hlocal
  obtain ⟨t, ht⟩ := hK.elim_nhdsWithin_subcover'
    (fun p hp => {x | h x - a ≤ C ⟨p, hp⟩ * ‖surfaceGradient n h x‖ ^ 2})
    (fun p hp => hbound ⟨p, hp⟩)
  have hsum : 0 ≤ ∑ p ∈ t, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
  refine ⟨1 + ∑ p ∈ t, C p, by linarith, ?_⟩
  intro x hx hxa hxb
  have hxK : x ∈ K := ⟨hx, hxa.le, hxb⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (ht hxK)
  exact hxp.trans (mul_le_mul_of_nonneg_right
    (le_trans (Finset.single_le_sum (fun q _ => (hC q).le) hp) (by linarith))
    (sq_nonneg _))

/-- `cor:sublevel-stable (i)`: the lower closed sublevel of a Morse function is
a strong deformation retract of the upper closed sublevel if `(a,b]` contains
no critical value. -/
theorem sublevel_deformation_retract_closed {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmorse : IsSurfaceMorse S n h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ioc a b) :
    let T := S ∩ {x | h x ≤ b}
    let A := S ∩ {x | h x ≤ a}
    ∃ H : ℝ → E₃ → E₃,
      ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ T) ∧
      (∀ q ∈ T, H 0 q = q) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ T, H s q ∈ T) ∧
      (∀ q ∈ T, H 1 q ∈ A) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q) :=
  sublevel_deformation_retract_closed_of_key hS hc hn hh hab hreg
    (exists_gradient_height_bound hS hc hn hh hmorse hab hreg)

/-- Both parts of `cor:sublevel-stable`, with their respective critical-value
exclusion hypotheses. -/
theorem sublevel_stable_retract {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmorse : IsSurfaceMorse S n h) {a b : ℝ} (hab : a < b) :
    let A := S ∩ {x | h x ≤ a}
    let Tclosed := S ∩ {x | h x ≤ b}
    let Topen := S ∩ {x | h x < b}
    ((∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ioc a b) →
      ∃ H : ℝ → E₃ → E₃,
        ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ Tclosed) ∧
        (∀ q ∈ Tclosed, H 0 q = q) ∧
        (∀ s ∈ Icc 0 1, ∀ q ∈ Tclosed, H s q ∈ Tclosed) ∧
        (∀ q ∈ Tclosed, H 1 q ∈ A) ∧
        (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q)) ∧
    ((∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ico a b) →
      ∃ H : ℝ → E₃ → E₃,
        ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ Topen) ∧
        (∀ q ∈ Topen, H 0 q = q) ∧
        (∀ s ∈ Icc 0 1, ∀ q ∈ Topen, H s q ∈ Topen) ∧
        (∀ q ∈ Topen, H 1 q ∈ A) ∧
        (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q)) :=
  ⟨fun hreg => sublevel_deformation_retract_closed hS hc hn hh hmorse hab hreg,
    fun hreg => sublevel_deformation_retract_open hS hc hn hh hab hreg⟩

end LiquidDrop
