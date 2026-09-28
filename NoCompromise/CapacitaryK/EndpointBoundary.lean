import NoCompromise.CapacitaryK.CollarGaussGreen
import NoCompromise.CapacitaryK.CollarContinuousFlux
import NoCompromise.CapacitaryK.EndpointFields
import NoCompromise.CapacitaryK.InequalitiesC2
import NoCompromise.CapacitaryK.LevelInequality

/-!
# `thm:capacitary-inequalities` in the blueprint's final form

For the capacitary potential `u` of `K` with a `C²` extension `g` across `∂K` (the standing
`thm:boundary-C2a` stand-in), the endpoint values are boundary integrals:

* `F(1) = lim_{t↑1} ∫_{u=t} |∇u|² = ∫_{∂K} |∇g|² dH²` (`levelF_tendsto_boundary`);
* `p(1) = lim_{t↑1} ∫_{u=t} H|∇u| = ∫_{∂K} H_g |∇g| dH²` (`levelP_tendsto_boundary`), where
  `H_g = meanCurv g` is the mean curvature of the level set of `g` through the point, i.e. of
  `∂K` with respect to its outward normal `ν_K = -∇g/|∇g|`.

The second limit uses `H|∇u| = ⟪-∇|∇g|, ν⟫` on the levels and on `∂K`: the field `-∇|∇g|` is
only continuous, so the collar Gauss–Green identity for `C¹` fields is transferred to it by
uniform approximation under the uniform area bound `H²{u = t} → H²(∂K)`.
-/

noncomputable section
open Real Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- The endpoint `p(1)`: `∫_{u=t} H|∇u| dH² → ∫_{∂K} H_g |∇g| dH²` as `t ↑ 1`. -/
theorem levelP_tendsto_boundary {K : Set E3} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    (hC2 : HasC2Boundary (interior K)) (hconn : IsPreconnected Kᶜ) :
    Tendsto (levelP Kᶜ u) (𝓝[<] 1)
      (𝓝 (∫ x in frontier K, meanCurv g x * gradNorm g x ∂hausdorffMeasure2 3)) := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ := capacitary_potential_contDiffOn hK hu hh
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  have hlt : ∀ x ∈ Kᶜ, u x < 1 := (capacitary_signs hK hzero hu hh hb hinf).2 hconn
  have hbd := gradient_eq_neg_norm_smul_normal hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
    hC2 hconn
  obtain ⟨t₁, ht₁, c, hc, r, hcolg⟩ := capacitary_collar_extension_gradient hK hreg hC1 hR₀
    hKR hzero hu hh hb hinf hg hug hC2 hconn
  have hcol : ∀ x ∈ closure Kᶜ, t₁ < u x → 0 < ‖gradient g x‖ :=
    fun x hx h => hc.trans_le (hcolg x hx h).1
  set s₁ : ℝ := (t₁ + 1) / 2 with hs₁def
  have hs₁ : t₁ < s₁ := by linarith
  have hs₁1 : s₁ < 1 := by linarith
  let C : Set E3 := closure Kᶜ ∩ u ⁻¹' Ici s₁
  have hCc : IsCompact C := by
    refine (isCompact_closedBall (0 : E3) r).of_isClosed_subset
      (isClosed_closure.inter (isClosed_Ici.preimage hu)) ?_
    intro x hx
    exact ball_subset_closedBall (hcolg x hx.1 (hs₁.trans_le hx.2)).2
  have hCg : ∀ x ∈ C, gradient g x ≠ 0 :=
    fun x hx => norm_pos_iff.mp (hcol x hx.1 (hs₁.trans_le hx.2))
  obtain ⟨Y, hY, hYeq⟩ := exists_continuous_neg_gradient_gradNorm hg hCc hCg
  have hYC : ∀ x ∈ C, Y x = -gradient (gradNorm g) x :=
    fun x hx => (hYeq.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
  have hsubK : ∀ s < 1, u ⁻¹' {s} ⊆ Kᶜ := by
    intro s hs x hx hxK
    have h1 : u x = s := hx
    rw [hb x hxK] at h1
    exact hs.ne' h1
  have hgradK : ∀ x ∈ Kᶜ, gradient u x = gradient g x :=
    fun x hx => (gradient_eventuallyEq_of_eqOn_closure hK.isClosed hug hx).2.eq_of_nhds
  have hlev : ∀ s ∈ Ioo t₁ 1, u ⁻¹' {s} ⊆ Kᶜ ∧ ∀ x, u x = s → gradient u x ≠ 0 := by
    intro s hs
    refine ⟨hsubK s hs.2, fun x hx => ?_⟩
    have hxK : x ∈ Kᶜ := hsubK s hs.2 hx
    rw [hgradK x hxK]
    exact norm_pos_iff.mp (hcol x (subset_closure hxK) (by rw [hx]; exact hs.1))
  have hfrC : frontier K ⊆ C := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have hx' : x ∈ frontier Kᶜ := by rwa [frontier_compl]
      exact frontier_subset_closure hx'
    · change s₁ ≤ u x
      rw [hb x (hK.isClosed.frontier_subset hx)]
      exact hs₁1.le
  have hSfin : hausdorffMeasure2 3 (frontier K) < ⊤ := by
    have h := capacity_boundary_measure_lt_top isOpen_interior
      (hK.isBounded.subset interior_subset) hC1
    rwa [capacity_frontier_interior hK hreg] at h
  have hA : ∃ A : ℝ, ∀ᶠ s in 𝓝[<] (1 : ℝ),
      hausdorffMeasure2 3 (u ⁻¹' {s}) ≤ ENNReal.ofReal A := by
    have harea := area_tendsto_boundary hK hreg hC1 hu hb hlt hinf hg hug ht₁ hcol
      (fun x hx => (hbd x hx).1)
    refine ⟨(hausdorffMeasure2 3 (frontier K)).toReal + 1, ?_⟩
    filter_upwards [(tendsto_order.1 harea).2 _ (lt_add_one _),
      eventually_level_measure_lt_top_of_collar hK hu hb hinf hg hug ht₁ hcol] with s hs hfin
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact ENNReal.ofReal_le_ofReal hs.le
  have hlim : ∀ Z : E3 → E3, ContDiff ℝ 1 Z → HasCompactSupport Z →
      Tendsto (fun s => ∫ x in u ⁻¹' {s}, ⟪Z x, unitNormal u x⟫ ∂(hausdorffMeasure2 3))
        (𝓝[<] 1) (𝓝 (∫ x in frontier K, ⟪Z x, hC1.outwardNormal x⟫ ∂(hausdorffMeasure2 3))) :=
    fun Z hZ _ => tendsto_collar_flux hK hreg hC1 hu hb hlt hinf hU (hsm.of_le (by norm_num))
      ht₁ hlev hZ
  have hνm : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable (unitNormal u) ((hausdorffMeasure2 3).restrict (u ⁻¹' {s})) := by
    filter_upwards [Ioo_mem_nhdsLT ht₁] with s hs
    refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_)
      ((isClosed_singleton.preimage hu).measurableSet)
    have hxK : x ∈ Kᶜ := hsubK s hs.2 hx
    have hu3 : ContDiffAt ℝ 3 u x := (hsm.contDiffAt (hU.mem_nhds hxK)).of_le (by norm_num)
    exact (unitNormal_contDiffAt_regular hu3
      (norm_pos_iff.mpr ((hlev s hs).2 x hx))).continuousAt.continuousWithinAt
  have hT := tendsto_flux_of_continuous (Sig := fun s => u ⁻¹' {s}) (S := frontier K)
    (ν := unitNormal u) (n := hC1.outwardNormal) hCc
    (by
      filter_upwards [Ioo_mem_nhdsLT hs₁1] with s hs x hx
      have hx' : u x = s := hx
      exact ⟨subset_closure (hsubK s hs.2 hx), show s₁ ≤ u x by rw [hx']; exact hs.1.le⟩)
    (Eventually.of_forall fun s => (isClosed_singleton.preimage hu).measurableSet)
    (Eventually.of_forall fun s x _ => norm_unitNormal_le u x) hνm hfrC
    isClosed_frontier.measurableSet (fun x _ => hC1.norm_outwardNormal_le x)
    (hC1.aestronglyMeasurable_outwardNormal _) hSfin hA hlim hY
  have hleft : (fun s => ∫ x in u ⁻¹' {s}, ⟪Y x, unitNormal u x⟫ ∂(hausdorffMeasure2 3))
      =ᶠ[𝓝[<] 1] levelP Kᶜ u := by
    filter_upwards [Ioo_mem_nhdsLT hs₁1] with s hs
    have hs1 : s < 1 := hs.2
    have hset : Kᶜ ∩ u ⁻¹' {s} = u ⁻¹' {s} := inter_eq_right.mpr (hsubK s hs1)
    rw [levelP, hset]
    refine setIntegral_congr_fun ((isClosed_singleton.preimage hu).measurableSet) fun x hx => ?_
    have hx' : u x = s := hx
    have hxK : x ∈ Kᶜ := hsubK s hs1 hx
    have hw : 0 < gradNorm u x :=
      norm_pos_iff.mpr ((hlev s ⟨hs₁.trans hs.1, hs1⟩).2 x hx)
    rw [hYC x ⟨subset_closure hxK, show s₁ ≤ u x by rw [hx']; exact hs.1.le⟩,
      meanCurv_mul_gradNorm_eq_of_exterior hK.isClosed hg hug hxK hw (hΔ x hxK)]
  have hright : (∫ x in frontier K, ⟪Y x, hC1.outwardNormal x⟫ ∂(hausdorffMeasure2 3)) =
      ∫ x in frontier K, meanCurv g x * gradNorm g x ∂hausdorffMeasure2 3 := by
    refine setIntegral_congr_fun isClosed_frontier.measurableSet fun x hx => ?_
    rw [hYC x (hfrC hx)]
    exact (meanCurv_mul_gradNorm_eq_of_boundary hg (hbd x hx).1 (hbd x hx).2
      (laplacianN_extension_eq_zero hK.isClosed hu hh hg hug x (hfrC hx).1)).symm
  rw [← hright]
  exact hT.congr' hleft

/-- Endpoint identification for the capacitary potential under the `C²` extension:
`F(1) := F(t₀) + ∫_{t₀}^1 p = ∫_{∂K} |∇g|²` and `p(1) := p(t₀) + μ{t₀ < u < 1} = ∫_{∂K} H_g|∇g|`. -/
theorem capacitary_endpoint_values_of_C2_extension
    {K : Set E3} (hK : IsCompact K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hC2 : HasC2Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    levelF Kᶜ u t₀ + ∫ t in t₀..1, Kp μ u t₀ (levelP Kᶜ u t₀) t =
        ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      levelP Kᶜ u t₀ + (μ (u ⁻¹' Ioo t₀ 1)).toReal =
        ∫ x in frontier K, meanCurv g x * gradNorm g x ∂hausdorffMeasure2 3 := by
  have hlt : ∀ x ∈ Kᶜ, u x < 1 := (capacitary_signs hK hzero hu hh hb hinf).2 hcompl
  have hbd := gradient_eq_neg_norm_smul_normal hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug
    hC2 hcompl
  obtain ⟨t₁, ht₁, c, hc, r, hcolg⟩ := capacitary_collar_extension_gradient hK hreg hC1 hR₀
    hKR hzero hu hh hb hinf hg hug hC2 hcompl
  exact capacitary_endpoint_values_of_level_limits hK hu hh hb hinf hμU hμK hμ ht₀ ht₀R
    (capacitary_collar_of_C2_extension hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug hC2
      hcompl)
    (levelF_tendsto_boundary hK hreg hC1 hu hb hlt hinf hg hug ht₁
      (fun x hx h => hc.trans_le (hcolg x hx h).1) (fun x hx => (hbd x hx).1))
    (levelP_tendsto_boundary hK hreg hC1 hR₀ hKR hzero hu hh hb hinf hg hug hC2 hcompl)

/-- Blueprint `thm:capacitary-inequalities` (`eq:capacitary-inequalities`) in its final form,
modulo only `thm:total-curvature-bound` and the `C²` extension `g` of `u` across `∂K`:
`∫_{∂K} |∇u|² ≥ 4π` and `∫_{∂K} H|∇u| ≥ 4 ∫_{∂K} |∇u|² - 8π`, with `∇u = ∇g` on `∂K` and
`H = meanCurv g` the mean curvature of `∂K` for the outward normal `ν_K = -∇g/|∇g|`. -/
theorem capacitary_inequalities_boundary_of_C2_extension
    {K : Set E3} (hK : IsCompact K) (hKconn : IsConnected K) (hcompl : IsPreconnected Kᶜ)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hC2 : HasC2Boundary (interior K))
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (hug : EqOn u g (closure Kᶜ))
    {μ : Measure E3} (hμU : μ Kᶜᶜ = 0)
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ Kᶜ, u x = t₀ → gradient u x ≠ 0) :
    4 * π ≤ ∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3 ∧
      4 * (∫ x in frontier K, ‖gradient g x‖ ^ 2 ∂hausdorffMeasure2 3) - 8 * π ≤
        ∫ x in frontier K, meanCurv g x * gradNorm g x ∂hausdorffMeasure2 3 := by
  obtain ⟨hF1, hp1⟩ := capacitary_endpoint_values_of_C2_extension hK hcompl hreg hC1 hC2 hR₀
    hKR hzero hu hh hb hinf hg hug hμU hμK hμ ht₀ ht₀R
  have h := capacitary_inequalities_of_C2_extension hK hKconn hcompl hreg hC1 hC2 hR₀ hKR hzero
    hu hh hb hinf hg hug hμU hμK hμ h_of_total_curvature_bound ht₀ ht₀R
  rw [hF1, hp1] at h
  exact h

end LiquidDrop.CapacitaryK
