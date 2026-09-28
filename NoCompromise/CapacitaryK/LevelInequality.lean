import NoCompromise.CapacitaryK.GaussEquation
import NoCompromise.CapacitaryK.PGeometric
import NoCompromise.CapacitaryK.DensityInput
import NoCompromise.CapacitaryK.MeasureInequality

/-!
# The pointwise measure inequality on a regular level (chapter 31, `prop:K-measure-inequality`)

`K_level_inequality` is `eq:K-measure-ineq-pointwise` on one compact regular level:
`(∫Hw)²/∫w² - 8π ≤ ∫(|A|² + |∇_Σ log w|²) = ∫ Δw/w`, from the Gauss equation `|A|² = H² - 2κ`,
`lem:K-gauss-bonnet-input` (`∫κ ≤ 4π`, with its two named external inputs) and Cauchy-Schwarz
(`K_measure_ineq_level`). Integrability of `κ` follows from the identity
`κ = (|∇w|²/w² - Δw/w)/2` on harmonic levels.
-/

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- A unit vector can be the last vector of an orthonormal frame. -/
lemma exists_frame_last (v : E3) (hv : ‖v‖ = 1) :
    ∃ f : OrthonormalBasis (Fin 3) ℝ E3, f 2 = v := by
  have ho : Orthonormal ℝ (({2} : Set (Fin 3)).domRestrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    subst j
    simp [hv]
  obtain ⟨f, hf⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp [E3])
  exact ⟨f, hf 2 (by simp)⟩

lemma unitNormal_contDiffAt_regular {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hw : 0 < gradNorm u x) :
    ContDiffAt ℝ 2 (unitNormal u) x := by
  have hg : ContDiffAt ℝ 2 (gradient u) x :=
    (toDual ℝ E3).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      (hu.fderiv_right (by norm_num))
  exact ((gradNorm_contDiffAt_of_pos hu hw).inv hw.ne' |>.smul hg).neg

lemma meanCurv_continuousAt_regular {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hw : 0 < gradNorm u x) :
    ContinuousAt (meanCurv u) x := by
  have hn := unitNormal_contDiffAt_regular hu hw
  have hd := (hn.fderiv_right (m := 1) (by norm_num)).continuousAt
  exact (tendsto_finsetSum _ fun i _ =>
    (hd.clm_apply continuousAt_const).inner continuousAt_const).sub
      ((hd.clm_apply hn.continuousAt).inner hn.continuousAt)

/-- The nonnegative tangential square term, without choosing a frame globally. -/
lemma level_density_sub_curvature_nonneg {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) {x : E3} (hx : x ∈ u ⁻¹' {t}) :
    0 ≤ laplacianN (gradNorm u) x / gradNorm u x -
      (meanCurv u x ^ 2 - 2 * gaussCurvature (u ⁻¹' {t}) (unitNormal u) x) := by
  have hw : 0 < gradNorm u x := norm_pos_iff.mpr (hreg x hx)
  have hn : ‖unitNormal u x‖ = 1 := by
    rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (gradNorm_nonneg u x)]
    exact inv_mul_cancel₀ hw.ne'
  obtain ⟨f, hf⟩ := exists_frame_last (unitNormal u x) hn
  have hs := contDiffOn_top_of_harmonic (by norm_num) hU (hu.of_le (by norm_num)) hΔ
  have hgauss := sum_secondFF_sq_eq_meanCurv_sq_sub_two_gaussCurvature
    hU hs hsub hreg hx f hf
  have hid := laplacianN_gradNorm_div_eq (hu.contDiffAt (hU.mem_nhds (hsub hx)))
    (Filter.eventually_of_mem (hU.mem_nhds (hsub hx)) hΔ) hw f hf
  rw [hid, hgauss, add_sub_cancel_left]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _


/-- `eq:K-measure-ineq-pointwise` on one regular level, assuming integrability of
its Gauss curvature with respect to surface measure. -/
theorem K_level_inequality_of_integrable {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) (hcompact : IsCompact (u ⁻¹' {t}))
    (hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤)
    (hFpos : 0 < levelF U u t)
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    (hκint : IntegrableOn (gaussCurvature (u ⁻¹' {t}) (unitNormal u)) (u ⁻¹' {t})
      (Measure.euclideanHausdorffMeasure 2)) :
    levelP U u t ^ 2 / levelF U u t - 8 * Real.pi ≤ levelDensity U u t := by
  classical
  let L := u ⁻¹' {t}
  let σ := (Measure.euclideanHausdorffMeasure 2).restrict L
  let A2 := fun x => meanCurv u x ^ 2 - 2 * gaussCurvature L (unitNormal u) x
  let g := L.indicator (fun x => laplacianN (gradNorm u) x / gradNorm u x - A2 x)
  have hLm : MeasurableSet L := hcompact.measurableSet
  have hwpos : ∀ x ∈ L, 0 < gradNorm u x := fun x hx => norm_pos_iff.mpr (hreg x hx)
  have hUL : U ∩ u ⁻¹' {t} = L := inter_eq_right.mpr hsub
  have hRL : (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} = L := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨⟨hsub hx, hwpos x hx⟩, hx⟩⟩
  have hHc : ContinuousOn (meanCurv u) L := fun x hx =>
    (meanCurv_continuousAt_regular (hu.contDiffAt (hU.mem_nhds (hsub hx)))
      (hwpos x hx)).continuousWithinAt
  have hwc : ContinuousOn (gradNorm u) L := (continuousOn_gradNorm hU hu).mono hsub
  have hDc : ContinuousOn (fun x => laplacianN (gradNorm u) x / gradNorm u x) L := by
    apply ContinuousOn.div _ hwc (fun x hx => (hwpos x hx).ne')
    exact (continuousOn_laplacianN_gradNorm_regular (isOpen_regularSet hU hu)
      (hu.mono inter_subset_left) (fun x hx => hx.2)).mono
        (fun x hx => ⟨hsub hx, hwpos x hx⟩)
  have hH2 : Integrable (fun x => meanCurv u x ^ 2) σ :=
    (hHc.pow 2).integrableOn_of_subset_isCompact hcompact hLm Subset.rfl hfin.ne
  have hw2 : Integrable (fun x => gradNorm u x ^ 2) σ :=
    (hwc.pow 2).integrableOn_of_subset_isCompact hcompact hLm Subset.rfl hfin.ne
  have hDi : Integrable (fun x => laplacianN (gradNorm u) x / gradNorm u x) σ :=
    hDc.integrableOn_of_subset_isCompact hcompact hLm Subset.rfl hfin.ne
  have hAi : Integrable A2 σ := hH2.sub (hκint.const_mul 2)
  have hg_eq : g =ᵐ[σ] (fun x => laplacianN (gradNorm u) x / gradNorm u x - A2 x) := by
    filter_upwards [ae_restrict_mem hLm] with x hx
    exact indicator_of_mem hx _
  have hgi : Integrable g σ := (hDi.sub hAi).congr hg_eq.symm
  have hg : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ L
    · rw [show g x = laplacianN (gradNorm u) x / gradNorm u x - A2 x from
        indicator_of_mem hx _]
      exact level_density_sub_curvature_nonneg hU hu hΔ hsub hreg hx
    · exact le_of_eq (indicator_of_notMem hx _).symm
  have hHw : AEStronglyMeasurable (fun x => meanCurv u x * gradNorm u x) σ :=
    (hHc.mul hwc).aestronglyMeasurable hLm
  have hκ := K_gauss_bonnet_input_of_harmonic hU (hu.of_le (by norm_num)) hΔ
    ht0 ht1 hsub hreg hcompact h_of_level_connected h_of_total_curvature_bound
  have hpos : 0 < ∫ x, gradNorm u x ^ 2 ∂σ := by
    simpa only [levelF, hUL] using hFpos
  obtain ⟨hfirst, hsecond⟩ := K_measure_ineq_level
    (A2 := A2) (g := g) (H := meanCurv u) (w := gradNorm u)
    (κ := gaussCurvature L (unitNormal u)) (fun _ => rfl) hg hH2 hw2 hκint hgi hκ hpos hHw
  have hident : (∫ x, (A2 x + g x) ∂σ) = levelDensity U u t := by
    rw [levelDensity, hRL]
    apply integral_congr_ae
    filter_upwards [hg_eq] with x hx
    rw [hx]
    ring
  rw [← hident]
  simpa only [levelP, levelF, hUL] using hsecond.trans hfirst


/-- For harmonic potentials the Gauss curvature has a frame-free expression in `w`. -/
lemma gaussCurvature_level_eq {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) {x : E3} (hx : x ∈ u ⁻¹' {t}) :
    gaussCurvature (u ⁻¹' {t}) (unitNormal u) x =
      (‖gradient (gradNorm u) x‖ ^ 2 / gradNorm u x ^ 2 -
        laplacianN (gradNorm u) x / gradNorm u x) / 2 := by
  have hw : 0 < gradNorm u x := norm_pos_iff.mpr (hreg x hx)
  have hn : ‖unitNormal u x‖ = 1 := by
    rw [unitNormal, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (gradNorm_nonneg u x)]
    exact inv_mul_cancel₀ hw.ne'
  obtain ⟨f, hf⟩ := exists_frame_last (unitNormal u x) hn
  have hs := contDiffOn_top_of_harmonic (by norm_num) hU (hu.of_le (by norm_num)) hΔ
  have hx3 := hu.contDiffAt (hU.mem_nhds (hsub hx))
  have hx2 : ContDiffAt ℝ 2 u x := hx3.of_le (by norm_num)
  have hgauss := sum_secondFF_sq_eq_meanCurv_sq_sub_two_gaussCurvature
    hU hs hsub hreg hx f hf
  have hid := laplacianN_gradNorm_div_eq hx3
    (Filter.eventually_of_mem (hU.mem_nhds (hsub hx)) hΔ) hw f hf
  rw [hgauss, Fin.sum_univ_two] at hid
  have hnorm := norm_gradient_sq_eq_sum_frame (x := x) (gradNorm u) f
  rw [Fin.sum_univ_three, hf, fderiv_gradNorm_unitNormal hx2 hw (hΔ x (hsub hx))] at hnorm
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at hid
  field_simp [hw.ne'] at hid ⊢
  nlinarith [hnorm]

/-- Gauss curvature is integrable on a compact regular level of finite surface measure. -/
lemma integrableOn_gaussCurvature_level {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) (hcompact : IsCompact (u ⁻¹' {t}))
    (hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤) :
    IntegrableOn (gaussCurvature (u ⁻¹' {t}) (unitNormal u)) (u ⁻¹' {t})
      (Measure.euclideanHausdorffMeasure 2) := by
  have hwpos : ∀ x ∈ u ⁻¹' {t}, 0 < gradNorm u x :=
    fun x hx => norm_pos_iff.mpr (hreg x hx)
  have hwc := (continuousOn_gradNorm hU hu).mono hsub
  have hgc : ContinuousOn (fun x => ‖gradient (gradNorm u) x‖ ^ 2) (u ⁻¹' {t}) := by
    intro x hx
    exact ((differentiableAt_gradient_of_contDiffAt
      (gradNorm_contDiffAt_of_pos (hu.contDiffAt (hU.mem_nhds (hsub hx)))
        (hwpos x hx))).continuousAt.norm.pow 2).continuousWithinAt
  have hDc : ContinuousOn (laplacianN (gradNorm u)) (u ⁻¹' {t}) :=
    (continuousOn_laplacianN_gradNorm_regular (isOpen_regularSet hU hu)
      (hu.mono inter_subset_left) (fun x hx => hx.2)).mono
        (fun x hx => ⟨hsub hx, hwpos x hx⟩)
  have hc : ContinuousOn (fun x =>
      (‖gradient (gradNorm u) x‖ ^ 2 / gradNorm u x ^ 2 -
        laplacianN (gradNorm u) x / gradNorm u x) / 2) (u ⁻¹' {t}) :=
    ((hgc.div (hwc.pow 2) (fun x hx => pow_ne_zero 2 (hwpos x hx).ne')).sub
      (hDc.div hwc (fun x hx => (hwpos x hx).ne'))).div_const 2
  have hκc : ContinuousOn (gaussCurvature (u ⁻¹' {t}) (unitNormal u)) (u ⁻¹' {t}) :=
    hc.congr (fun x hx => gaussCurvature_level_eq hU hu hΔ hsub hreg hx)
  exact hκc.integrableOn_of_subset_isCompact hcompact hcompact.measurableSet Subset.rfl hfin.ne

/-- `eq:K-measure-ineq-pointwise` on one regular level:
`p²/F − 8π ≤ ∫_{u=t}(|A|² + |∇_Σ log w|²)`. -/
theorem K_level_inequality {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hsub : u ⁻¹' {t} ⊆ U)
    (hreg : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0) (hcompact : IsCompact (u ⁻¹' {t}))
    (hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤)
    (hFpos : 0 < levelF U u t)
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi) :
    levelP U u t ^ 2 / levelF U u t - 8 * Real.pi ≤ levelDensity U u t :=
  K_level_inequality_of_integrable hU hu hΔ ht0 ht1 hsub hreg hcompact hfin hFpos
    h_of_level_connected h_of_total_curvature_bound
    (integrableOn_gaussCurvature_level hU hu hΔ hsub hreg hcompact hfin)

end LiquidDrop.CapacitaryK
