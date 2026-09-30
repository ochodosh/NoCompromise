module

public import NoCompromise.CapacitaryK.LevelFrame
public import NoCompromise.CapacitaryK.PositiveMeasure
public import NoCompromise.BV.CoareaL1Lebesgue

@[expose] public section

/-!
# Coarea identities for the capacitary gradient length

The coarea half of `lem:K-slab-F` and the regular-set density formula of
`lem:K-pushforward-density` in chapter 31 (`cor:coarea-L1`, `coarea_L1_nullMeasurable`).

* `K_slab_F_coarea`: `∫_{a<u<b} ∇w·∇u = ∫_a^b ∫_{u=t, w>0} Hw dH² dt`; on `{w = 0}` the
  integrand vanishes since `∇u = 0`, and on `{w > 0}` it equals `Hw · w` by `∂_ν w = -Hw`.
  The first equality `F(b) - F(a) = ∫_{a<u<b} ∇w·∇u` (Gauss-Green on the slab) is
  `K_slab_F_gauss_green_of_gauss_green` (`SlabH.lean`); the assembled lemma is `K_slab_F`
  (`PGeometric.lean`).
* `K_pushforward_density_coarea` and `laplacianN_gradNorm_div_eq`: for Borel `B`,
  `∫_{U∩{w>0}∩u⁻¹B} Δw = ∫_B ∫_{u=t, w>0} Δw/w dH² dt` with
  `Δw/w = |A|² + |∇_Σ log w|²`. The identification of `μ` with `Δw dx` on `{w > 0}` is
  `K_mu_restrict_regular` (`MuRegular.lean`), used in `K_pushforward_density`.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- On a regular harmonic level, the slab integrand divided by `w` is `H w`. -/
lemma inner_gradient_gradNorm_div_eq {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 2 u x) (hw : 0 < gradNorm u x)
    (hΔ : laplacianN u x = 0) :
    ⟪gradient (gradNorm u) x, gradient u x⟫ / gradNorm u x =
      meanCurv u x * gradNorm u x := by
  rw [inner_gradient_eq_fderiv, gradient_eq_neg_smul_unitNormal hw,
    map_neg, map_smul, smul_eq_mul, fderiv_gradNorm_unitNormal hu hw hΔ]
  field_simp

/-- `lem:K-slab-F`, coarea half: on the part of the slab `{a < u < b}` inside the open set `U`
where `u` is `C³` and harmonic, `∫ ∇w·∇u dx = ∫_a^b ∫_{u=t, w>0} H w dH² dt`. -/
theorem K_slab_F_coarea {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {a b : ℝ}
    (hint : IntegrableOn (fun x => ⟪gradient (gradNorm u) x, gradient u x⟫) (U ∩ u ⁻¹' Ioo a b)) :
    ∫ x in U ∩ u ⁻¹' Ioo a b, ⟪gradient (gradNorm u) x, gradient u x⟫ =
      ∫ t in Ioo a b, ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
        meanCurv u x * gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  have hA : MeasurableSet (U ∩ u ⁻¹' Ioo a b) :=
    (hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo).measurableSet
  have hgrad : Measurable (gradient u) :=
    (toDual ℝ E3).symm.continuous.measurable.comp (measurable_fderiv ℝ u)
  have hreg : MeasurableSet {x | 0 < gradNorm u x} :=
    measurableSet_lt measurable_const hgrad.norm
  have hsource :
      (∫ x in U ∩ u ⁻¹' Ioo a b, ⟪gradient (gradNorm u) x, gradient u x⟫) =
        ∫ x in (U ∩ u ⁻¹' Ioo a b) ∩ {x | 0 < ‖gradient u x‖},
          ⟪gradient (gradNorm u) x, gradient u x⟫ := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA inter_subset_left
    intro x hx
    have hw : ¬ 0 < ‖gradient u x‖ := fun hw => hx.2 ⟨hx.1, hw⟩
    have hz : gradient u x = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp hw) (norm_nonneg _))
    simp [hz]
  obtain ⟨_, _, he⟩ := coarea_L1_nullMeasurable (by norm_num : 2 ≤ 3) hU
    (hu.of_le (by norm_num)) hA.nullMeasurableSet inter_subset_left hint
  rw [hsource, he]
  change (∫ t : ℝ, ∫ x in ((U ∩ u ⁻¹' Ioo a b) ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
      ⟪gradient (gradNorm u) x, gradient u x⟫ / gradNorm u x
        ∂Measure.euclideanHausdorffMeasure 2) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b) (fun t ht => ?_)]
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have hset : ((U ∩ u ⁻¹' Ioo a b) ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} =
        (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨hxU, _⟩, hw⟩, hxt⟩
        exact ⟨⟨hxU, hw⟩, hxt⟩
      · rintro ⟨⟨hxU, hw⟩, hxt⟩
        exact ⟨⟨⟨hxU, hxt ▸ ht⟩, hw⟩, hxt⟩
    dsimp only
    rw [hset]
    apply setIntegral_congr_fun
      (measurableSet_coarea_level_of_continuousOn (hU.measurableSet.inter hreg)
        (hu.continuousOn.mono inter_subset_left) t)
    intro x hx
    exact inner_gradient_gradNorm_div_eq
      ((hu.contDiffAt (hU.mem_nhds hx.1.1)).of_le (by norm_num)) hx.1.2 (hΔ x hx.1.1)
  · have hset : ((U ∩ u ⁻¹' Ioo a b) ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨⟨_, hxab⟩, _⟩, hxt⟩
      exact ht ((mem_singleton_iff.mp hxt) ▸ hxab)
    simp [hset]

/-- `lem:K-pushforward-density`, coarea identity on the regular set: for a Borel set `B` of
levels, the mass of `Δw dx` on `U ∩ {w>0} ∩ u⁻¹B` is `∫_B ∫_{u=t, w>0} Δw / w dH² dt`; by
`laplacianN_gradNorm_div_eq`, `Δw / w = |A|² + |∇_Σ log w|²` on `{w > 0}`. -/
theorem K_pushforward_density_coarea {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {B : Set ℝ} (hB : MeasurableSet B)
    (hint : IntegrableOn (laplacianN (gradNorm u)) ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B)) :
    ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B, laplacianN (gradNorm u) x =
      ∫ t in B, ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
        laplacianN (gradNorm u) x / gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  classical
  have hR : MeasurableSet (U ∩ {x | 0 < gradNorm u x}) :=
    ((continuousOn_gradNorm hU hu).isOpen_inter_preimage hU isOpen_Ioi).measurableSet
  let v := U.piecewise u (fun _ => 0)
  have hv : Measurable v :=
    hu.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hA : MeasurableSet ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) := by
    have hset : (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B =
        (U ∩ {x | 0 < gradNorm u x}) ∩ v ⁻¹' B := by
      ext x
      by_cases hx : x ∈ U <;> simp [v, hx]
    rw [hset]
    exact hR.inter (hv hB)
  obtain ⟨_, _, he⟩ := coarea_L1_nullMeasurable (by norm_num : 2 ≤ 3) hU
    (hu.of_le (by norm_num)) hA.nullMeasurableSet (fun _ hx => hx.1.1) hint
  have hcut : ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) ∩ {x | 0 < ‖gradient u x‖} =
      (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B :=
    inter_eq_left.mpr (fun _ hx => hx.1.2)
  rw [hcut] at he
  rw [he]
  change (∫ t : ℝ, ∫ x in ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) ∩ u ⁻¹' {t},
      laplacianN (gradNorm u) x / gradNorm u x ∂Measure.euclideanHausdorffMeasure 2) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun t ht => ?_)]
  · apply setIntegral_congr_fun hB
    intro t ht
    have hset : ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) ∩ u ⁻¹' {t} =
        (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hx, _⟩, hxt⟩
        exact ⟨hx, hxt⟩
      · rintro ⟨hx, hxt⟩
        exact ⟨⟨hx, hxt ▸ ht⟩, hxt⟩
    dsimp only
    rw [hset]
  · have hset : ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' B) ∩ u ⁻¹' {t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨_, hxB⟩, hxt⟩
      exact ht ((mem_singleton_iff.mp hxt) ▸ hxB)
    simp [hset]

/-- Dividing the regular-set Laplacian identity by `w` gives the squared norm
of the second fundamental form plus the squared tangential logarithmic derivatives. -/
lemma laplacianN_gradNorm_div_eq {u : E3 → ℝ} {x : E3}
    (hu : ContDiffAt ℝ 3 u x) (hΔ : ∀ᶠ y in 𝓝 x, laplacianN u y = 0)
    (hw : 0 < gradNorm u x)
    (f : OrthonormalBasis (Fin 3) ℝ E3) (hf : f 2 = unitNormal u x) :
    laplacianN (gradNorm u) x / gradNorm u x =
      (∑ a : Fin 2, ∑ b : Fin 2, secondFF u x (f a.castSucc) (f b.castSucc) ^ 2) +
        ∑ a : Fin 2, (fderiv ℝ (gradNorm u) x (f a.castSucc) / gradNorm u x) ^ 2 := by
  have hid := (K_level_identities hu hΔ hw f hf).2.2.2.2.2
  rw [hid.1, hid.2]
  simp_rw [div_pow, ← Finset.sum_div]
  field_simp

end LiquidDrop.CapacitaryK
