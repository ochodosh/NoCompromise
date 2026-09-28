import NoCompromise.CapacitaryK.MuRegular
import NoCompromise.CapacitaryK.SlabCoarea
import NoCompromise.Sard.ThreeDimensional

/-!
# Density of `u_#μ` on the regular set (`lem:K-pushforward-density`, chapter 31)

For `u` of class `C³` and harmonic on an open `U ⊆ ℝ³`, and `μ` the measure representing the
distribution `Δ|∇u|` on `U` (as produced by `K_mu_measure`, `prop:K-mu`), write
`R = U ∩ {w > 0}` for the regular set and `Crit = U ∩ {∇u = 0}` for the critical set.

* `μ (R ∩ u⁻¹B) = ∫_B ∫_{u=t, w>0} Δw / w dH² dt` for Borel `B` of finite mass
  (`K_mu_restrict_regular` and `cor:coarea-L1`); pointwise `Δw / w = |A|² + |∇_Σ log w|²`
  (`laplacianN_gradNorm_div_eq`), which is `eq:K-pushforward-density`.
* `μ (u⁻¹B) = μ (R ∩ u⁻¹B) + μ (Crit ∩ u⁻¹B)`: `u_#μ` is the sum of the absolutely continuous
  regular part and the nonnegative critical part `u_#(μ|_Crit)`.
* On sets `B` of regular values the critical part vanishes, and the critical part is carried by
  a Borel Lebesgue-null set `N ⊇ u(Crit)` (`thm:sard-3d`), so it is singular.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- On the regular set, `μ` is `Δw dx`, evaluated on arbitrary subsets. -/
lemma K_mu_regular_inter_eq {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ) (A : Set E3) :
    μ (U ∩ {x | 0 < gradNorm u x} ∩ A) =
      ∫⁻ x in U ∩ {x | 0 < gradNorm u x} ∩ A, ENNReal.ofReal (laplacianN (gradNorm u) x) := by
  have hR : MeasurableSet (U ∩ {x | 0 < gradNorm u x}) :=
    (isOpen_regularSet hU hu).measurableSet
  have h := K_mu_restrict_regular hU hu hΔ hμK hμ
  have h1 : μ (U ∩ {x | 0 < gradNorm u x} ∩ A) =
      μ.restrict (U ∩ {x | 0 < gradNorm u x}) A := by
    rw [Measure.restrict_apply' hR, inter_comm]
  rw [h1, h, withDensity_apply' _ A, Measure.restrict_restrict' hR, inter_comm]

lemma measurableSet_regular_inter_preimage {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) := by
  classical
  have hR : MeasurableSet (U ∩ {x | 0 < gradNorm u x}) :=
    (isOpen_regularSet hU hu).measurableSet
  let v := U.piecewise u (fun _ => 0)
  have hv : Measurable v :=
    hu.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hset : (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B =
      (U ∩ {x | 0 < gradNorm u x}) ∩ v ⁻¹' B := by
    ext x
    by_cases hx : x ∈ U <;> simp [v, hx]
  rw [hset]
  exact hR.inter (hv hB)

/-- `lem:K-pushforward-density`. -/
theorem K_pushforward_density {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ) :
    (∀ B : Set ℝ, MeasurableSet B → μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' B) ≠ ⊤ →
      (μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' B)).toReal =
        ∫ t in B, ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
          laplacianN (gradNorm u) x / gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)) ∧
    (∀ B : Set ℝ, MeasurableSet B → μ (u ⁻¹' B) =
      μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' B) + μ (U ∩ {x | gradient u x = 0} ∩ u ⁻¹' B)) ∧
    (∀ B : Set ℝ, (∀ x ∈ U, u x ∈ B → gradient u x ≠ 0) →
      μ (U ∩ {x | gradient u x = 0} ∩ u ⁻¹' B) = 0) ∧
    ∃ N : Set ℝ, MeasurableSet N ∧ volume N = 0 ∧ u '' (U ∩ {x | gradient u x = 0}) ⊆ N ∧
      μ (U ∩ {x | gradient u x = 0} ∩ u ⁻¹' Nᶜ) = 0 := by
  set R := U ∩ {x | 0 < gradNorm u x} with hRdef
  set Cr := U ∩ {x | gradient u x = 0} with hCrdef
  have hRm : MeasurableSet R := (isOpen_regularSet hU hu).measurableSet
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ E3).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hCm : MeasurableSet Cr :=
    hU.measurableSet.inter (measurableSet_eq_fun hgrad measurable_const)
  have hnonneg : ∀ x ∈ R, 0 ≤ laplacianN (gradNorm u) x := by
    intro x hx
    apply laplacianN_gradNorm_nonneg_of_pos (hu.contDiffAt (hU.mem_nhds hx.1)) _ hx.2
    filter_upwards [hU.mem_nhds hx.1] with y hy
    exact hΔ y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB hfin
    have hA := measurableSet_regular_inter_preimage hU hu hB
    have hc : ContinuousOn (laplacianN (gradNorm u)) R :=
      continuousOn_laplacianN_gradNorm_regular (isOpen_regularSet hU hu) (hu.mono inter_subset_left)
        (fun _ hx => hx.2)
    have hmeas : AEStronglyMeasurable (laplacianN (gradNorm u))
        (volume.restrict (R ∩ u ⁻¹' B)) :=
      (hc.mono inter_subset_left).aestronglyMeasurable hA
    have hnn : 0 ≤ᵐ[volume.restrict (R ∩ u ⁻¹' B)] laplacianN (gradNorm u) := by
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hnonneg x hx.1
    have hmass := K_mu_regular_inter_eq hU hu hΔ hμK hμ (u ⁻¹' B)
    have hint : IntegrableOn (laplacianN (gradNorm u)) (R ∩ u ⁻¹' B) := by
      refine ⟨hmeas, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn, ← hmass]
      exact lt_top_iff_ne_top.mpr hfin
    rw [← K_pushforward_density_coarea hU hu hB hint, hmass,
      integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  · intro B hBm
    have hsplit : u ⁻¹' B ∩ U = (R ∩ u ⁻¹' B) ∪ (Cr ∩ u ⁻¹' B) := by
      ext x
      simp only [hRdef, hCrdef, mem_inter_iff, mem_preimage, mem_union, mem_ofPred_eq,
        gradNorm]
      constructor
      · rintro ⟨hxB, hxU⟩
        by_cases h0 : gradient u x = 0
        · exact Or.inr ⟨⟨hxU, h0⟩, hxB⟩
        · exact Or.inl ⟨⟨hxU, norm_pos_iff.mpr h0⟩, hxB⟩
      · rintro (⟨⟨hxU, _⟩, hxB⟩ | ⟨⟨hxU, _⟩, hxB⟩) <;> exact ⟨hxB, hxU⟩
    have hdisj : Disjoint (R ∩ u ⁻¹' B) (Cr ∩ u ⁻¹' B) := by
      rw [Set.disjoint_left]
      rintro x ⟨⟨_, hx⟩, _⟩ ⟨⟨_, hx0⟩, _⟩
      simp only [mem_ofPred_eq, gradNorm] at hx hx0
      rw [hx0, norm_zero] at hx
      exact lt_irrefl _ hx
    have hU' : μ (u ⁻¹' B) = μ (u ⁻¹' B ∩ U) := by
      apply le_antisymm
      · calc μ (u ⁻¹' B) ≤ μ (u ⁻¹' B ∩ U ∪ Uᶜ) := measure_mono (fun x hx => by
              by_cases hxU : x ∈ U
              · exact Or.inl ⟨hx, hxU⟩
              · exact Or.inr hxU)
          _ ≤ μ (u ⁻¹' B ∩ U) + μ Uᶜ := measure_union_le _ _
          _ = μ (u ⁻¹' B ∩ U) := by rw [hμU, add_zero]
      · exact measure_mono inter_subset_left
    rw [hU', hsplit, measure_union' hdisj (measurableSet_regular_inter_preimage hU hu hBm)]
  · intro B hB
    have he : Cr ∩ u ⁻¹' B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨hxU, hx0⟩, hxB⟩
      exact hB x hxU hxB hx0
    rw [he, measure_empty]
  · refine ⟨toMeasurable volume (u '' Cr), measurableSet_toMeasurable _ _, ?_,
      subset_toMeasurable _ _, ?_⟩
    · rw [measure_toMeasurable]
      exact LiquidDrop.sard_three_dimensional_gradient hU hu
    · have he : Cr ∩ u ⁻¹' (toMeasurable volume (u '' Cr))ᶜ = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxN⟩
        exact hxN (subset_toMeasurable _ _ (mem_image_of_mem u hx))
      rw [he, measure_empty]

end LiquidDrop.CapacitaryK
