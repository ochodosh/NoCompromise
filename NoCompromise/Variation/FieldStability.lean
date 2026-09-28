import NoCompromise.Variation.FieldInterpolation
import NoCompromise.Sobolev.Extension

/-!
# Stability of BV pullbacks under changes of the field

For globally Lipschitz C¹ fields with `|t| L < 1/2`, inverse pullbacks differ in
L¹ by at most `16 |t|` times the local field difference and the BV variation.
Every intermediate inverse image is explicitly required to lie in the open
comparison domain. Strict approximation on that domain proves the estimate for
BV functions; no convergence of pointwise representatives is assumed.

The compactly supported specialization uses the true derivative sup norms and
the local essential supremum of the field difference. The integration set only
needs to be measurable, so the result includes the blueprint's compact-set and
nested-neighborhood formulation.
-/

noncomputable section
open Set Function Filter MeasureTheory InnerProductSpace
open scoped Topology NNReal ENNReal Gradient
namespace LiquidDrop

lemma lintegral_comp_le_of_lipschitz_leftInverse {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΦ : ContinuousOn Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in U, g (Φ x)) ≤ (K : ℝ≥0∞)^n * ∫⁻ x in V, g x := by
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse hU hΦ hΨ hmaps hinv
  calc
    _ = ∫⁻ x, g x ∂Measure.map Φ (volume.restrict U) :=
      (lintegral_map' hg.aemeasurable (hΦ.aemeasurable hU)).symm
    _ ≤ ∫⁻ x, g x ∂((K : ℝ≥0∞)^n • volume.restrict V) := lintegral_mono' hmap le_rfl
    _ = _ := by rw [lintegral_smul_measure]; rfl

/-- The smooth stability estimate uses only the actual interpolated inverse images
of the integration set, and a field - difference bound on their open neighborhood. -/
theorem smooth_field_stability {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V)
    {u : AmbientSpace → ℝ} (hu : ContDiffOn ℝ 1 u V)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫⁻ z in K, ‖u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)‖ₑ) ≤
      ENNReal.ofReal (16 * |t| * M) * ∫⁻ x in V, ‖gradient u x‖ₑ := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  let q : ℝ × AmbientSpace → AmbientSpace := fun p => interpolatedInverse X Y t p.1 p.2
  let g : AmbientSpace → ℝ≥0∞ := fun x => ENNReal.ofReal ‖fderiv ℝ u x‖
  have hgm : Measurable g := (measurable_fderiv ℝ u).norm.ennreal_ofReal
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1 ×ˢ K) :=
    (contDiffOn_interpolatedInverse_Icc hX hY hXC hYC ht1).continuousOn.mono
      (prod_mono Subset.rfl (subset_univ _))
  have hqmap : MapsTo q (Icc (0 : ℝ) 1 ×ˢ K) V := fun p hp => hpath p.1 hp.1 hp.2
  have hj : AEMeasurable (fun p : ℝ × AmbientSpace => g (q p))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact (((hu.continuousOn_fderiv_of_isOpen hV (by norm_num)).norm.comp
      hqc hqmap).aemeasurable
      (measurableSet_Icc.prod hK)).ennreal_ofReal
  have hi (s : ℝ) (hs : s ∈ Icc 0 1) :
      (∫⁻ z in K, g (interpolatedInverse X Y t s z)) ≤ 8 * ∫⁻ x in V, g x := by
    let e := straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht1
    have he : interpolatedInverse X Y t s = e.symm :=
      interpolatedInverse_eq_homeomorph hX hY ht1 hs
    have hl : LipschitzWith 2 e := by
      apply (lipschitzWith_straightPerturbation
        (lipschitzWith_interpolatedField_Icc hX hY hs) t).weaken
      exact_mod_cast (show 1 + |t| * (L : ℝ) ≤ 2 by linarith)
    have hmaps : MapsTo e.symm K V := he ▸ hpath s hs
    have h := lintegral_comp_le_of_lipschitz_leftInverse hK e.symm.continuous.continuousOn
      hl.lipschitzOnWith hmaps (fun z _ => e.apply_symm_apply z) hgm
    simpa only [he, ENNReal.coe_ofNat, show (2 : ℝ≥0∞)^3 = 8 by norm_num] using h
  have hgrad : g = fun x => ‖gradient u x‖ₑ := by
    funext x
    dsimp [g]
    rw [← ofReal_norm]
    congr 1
    exact ((toDual ℝ AmbientSpace).symm.norm_map (fderiv ℝ u x)).symm
  calc
    _ ≤ ∫⁻ z in K, ENNReal.ofReal (2 * |t| * M) *
        ∫⁻ s in Icc (0 : ℝ) 1, g (interpolatedInverse X Y t s z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK] with z hz
      exact enorm_comp_interpolatedInverse_sub_le hX hY hXC hYC z ht hV hu
        (fun s hs => hpath s hs hz) hM hbound
    _ = ENNReal.ofReal (2 * |t| * M) *
        ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ z in K, g (interpolatedInverse X Y t s z) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact (lintegral_lintegral_swap hj).symm
    _ ≤ ENNReal.ofReal (2 * |t| * M) *
        ∫⁻ s in Icc (0 : ℝ) 1, 8 * ∫⁻ x in V, g x := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hi s hs
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        sub_zero, ENNReal.ofReal_one, mul_one, hgrad]
      rw [← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Real - integral form of the smooth estimate. -/
theorem integral_smooth_field_stability {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V)
    {u : AmbientSpace → ℝ} (hu : ContDiffOn ℝ 1 u V)
    (hi : IntegrableOn u V) (hig : IntegrableOn (gradient u) V)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫ z in K, |u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)|) ≤
      (16 * |t| * M) * ∫ x in V, ‖gradient u x‖ := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  have hiq (s : ℝ) (hs : s ∈ Icc 0 1) :
      IntegrableOn (u ∘ interpolatedInverse X Y t s) K := by
    let e := straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht1
    have he : interpolatedInverse X Y t s = e.symm :=
      interpolatedInverse_eq_homeomorph hX hY ht1 hs
    rw [he]
    exact integrableOn_comp_of_lipschitz_leftInverse hK e.symm.continuous.continuousOn
      (lipschitzWith_straightPerturbation
        (lipschitzWith_interpolatedField_Icc hX hY hs) t).lipschitzOnWith
      (he ▸ hpath s hs) (fun z _ => e.apply_symm_apply z) hi
  have hid : IntegrableOn (fun z => u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)) K := (hiq 1 (by simp)).sub (hiq 0 (by simp))
  have h := smooth_field_stability hX hY hXC hYC ht hK hV hu hpath hM hbound
  rw [← ofReal_integral_norm_eq_lintegral_enorm hid,
    ← ofReal_integral_norm_eq_lintegral_enorm hig,
    ← ENNReal.ofReal_mul (by positivity)] at h
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hreal
  simpa only [Real.norm_eq_abs] using hreal

/-- Quantitative field stability for BV functions. The set being integrated need
only be measurable; every intermediate inverse image must lie in the open BV domain. -/
theorem field_stability {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V)
    {u : AmbientSpace → ℝ} (hu : IsBVOn u V)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫ z in K, |u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)|) ≤
      (16 * |t| * M) * (variation u V).toReal := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  obtain ⟨g, hg, hie, he, _, hstrict⟩ := strict_approximation_on hV
    (isLocallyBVOn_of_variation_lt_top hV hu.1.locallyIntegrableOn hu.2)
  obtain ⟨hig, hgrad⟩ := hstrict hu.2
  have hgi (j) : IntegrableOn (g j) V := by
    have h := (hie j).add hu.1
    change IntegrableOn (fun x => (g j x - u x) + u x) V at h
    simpa only [sub_add_cancel] using h
  have hiq {f : AmbientSpace → ℝ} (hf : IntegrableOn f V)
      (s : ℝ) (hs : s ∈ Icc 0 1) :
      IntegrableOn (f ∘ interpolatedInverse X Y t s) K := by
    let e := straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht1
    have heq : interpolatedInverse X Y t s = e.symm :=
      interpolatedInverse_eq_homeomorph hX hY ht1 hs
    rw [heq]
    exact integrableOn_comp_of_lipschitz_leftInverse hK e.symm.continuous.continuousOn
      (lipschitzWith_straightPerturbation
        (lipschitzWith_interpolatedField_Icc hX hY hs) t).lipschitzOnWith
      (heq ▸ hpath s hs) (fun z _ => e.apply_symm_apply z) hf
  have herr (s : ℝ) (hs : s ∈ Icc 0 1) :
      Tendsto (fun j => ∫ z in K, |g j (interpolatedInverse X Y t s z) -
        u (interpolatedInverse X Y t s z)|) atTop (𝓝 0) := by
    let e := straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht1
    have heq : interpolatedInverse X Y t s = e.symm :=
      interpolatedInverse_eq_homeomorph hX hY ht1 hs
    have hb (j) := integral_norm_comp_le_of_lipschitz_leftInverse hK
      e.symm.continuous.continuousOn
      (lipschitzWith_straightPerturbation
        (lipschitzWith_interpolatedField_Icc hX hY hs) t).lipschitzOnWith
      (heq ▸ hpath s hs) (fun z _ => e.apply_symm_apply z) (hie j)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_)
      (by simpa only [mul_zero] using he.const_mul ((1 + |t| * (L : ℝ))^3))
    simpa only [heq, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
      coe_nnnorm, Function.comp_def] using hb j
  let q := interpolatedInverse X Y t
  have hstep (j : ℕ) : (∫ z in K, |u (q 1 z) - u (q 0 z)|) ≤
      (∫ z in K, |g j (q 1 z) - u (q 1 z)|) +
      (16 * |t| * M) * (∫ x in V, ‖gradient (g j) x‖) +
      (∫ z in K, |g j (q 0 z) - u (q 0 z)|) := by
    have h01 : IntegrableOn (fun z => u (q 1 z) - u (q 0 z)) K :=
      (hiq hu.1 1 (by simp)).sub (hiq hu.1 0 (by simp))
    have he1 : IntegrableOn (fun z => g j (q 1 z) - u (q 1 z)) K := hiq (hie j) 1 (by simp)
    have he0 : IntegrableOn (fun z => g j (q 0 z) - u (q 0 z)) K := hiq (hie j) 0 (by simp)
    have hg01 : IntegrableOn (fun z => g j (q 1 z) - g j (q 0 z)) K :=
      (hiq (hgi j) 1 (by simp)).sub (hiq (hgi j) 0 (by simp))
    have he01 : IntegrableOn (fun z => |g j (q 1 z) - u (q 1 z)| +
        |g j (q 1 z) - g j (q 0 z)|) K := he1.abs.add hg01.abs
    calc
      _ ≤ ∫ z in K, (|g j (q 1 z) - u (q 1 z)| +
          |g j (q 1 z) - g j (q 0 z)|) + |g j (q 0 z) - u (q 0 z)| := by
        apply integral_mono h01.abs ((he1.abs.add hg01.abs).add he0.abs)
        intro z
        change |u (q 1 z) - u (q 0 z)| ≤
          |g j (q 1 z) - u (q 1 z)| + |g j (q 1 z) - g j (q 0 z)| +
            |g j (q 0 z) - u (q 0 z)|
        have h := abs_add_three (u (q 1 z) - g j (q 1 z))
          (g j (q 1 z) - g j (q 0 z)) (g j (q 0 z) - u (q 0 z))
        simpa only [sub_add_sub_cancel, abs_sub_comm (u (q 1 z))] using h
      _ = (∫ z in K, |g j (q 1 z) - u (q 1 z)|) +
          (∫ z in K, |g j (q 1 z) - g j (q 0 z)|) +
          (∫ z in K, |g j (q 0 z) - u (q 0 z)|) := by
        rw [integral_add he01 he0.abs, integral_add he1.abs hg01.abs]
      _ ≤ _ := by
        gcongr
        exact integral_smooth_field_stability hX hY hXC hYC ht hK hV
          ((hg j).of_le (by simp)) (hgi j) (hig j) hpath hM hbound
  have hlim := ((herr 1 (by simp)).add (hgrad.const_mul (16 * |t| * M))).add
    (herr 0 (by simp))
  simpa only [zero_add, add_zero] using ge_of_tendsto hlim (Eventually.of_forall hstep)

/-- The BV estimate localized to an open subdomain of the original BV domain. -/
theorem field_stability_on {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V U : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V) (hU : IsOpen U) (hVU : V ⊆ U)
    {u : AmbientSpace → ℝ} (hu : IsBVOn u U)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫ z in K, |u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)|) ≤
      (16 * |t| * M) * (variation u V).toReal :=
  field_stability hX hY hXC hYC ht hK hV
    ⟨hu.1.mono_set hVU, (variation_mono hU.measurableSet hVU).trans_lt hu.2⟩ hpath hM hbound

/-- Local BV suffices when the inverse trajectories lie in a relatively compact open set. -/
theorem local_field_stability {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V U : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V)
    (hcV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    {u : AmbientSpace → ℝ} (hu : IsLocallyBVOn u U)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫ z in K, |u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)|) ≤
      (16 * |t| * M) * (variation u V).toReal :=
  field_stability hX hY hXC hYC ht hK hV
    ⟨(hu.1.integrableOn_compact_subset hVU hcV).mono_set subset_closure,
      hu.2 V hV hcV hVU⟩ hpath hM hbound

/-- On an open Euclidean set, the essential supremum of a continuous bounded
function bounds its norm at every point. -/
lemma norm_le_eLpNormEssSup_on_open {F : Type*} [NormedAddCommGroup F]
    {f : AmbientSpace → F} (hf : Continuous f) {V : Set AmbientSpace} (hV : IsOpen V)
    (hfin : eLpNormEssSup f (volume.restrict V) ≠ ∞) :
    ∀ x ∈ V, ‖f x‖ ≤ (eLpNormEssSup f (volume.restrict V)).toReal := by
  let M := (eLpNormEssSup f (volume.restrict V)).toReal
  have hb : ∀ᵐ x ∂volume.restrict V, ‖f x‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f (volume.restrict V)] with x hx
    simpa only [toReal_enorm] using ENNReal.toReal_mono hfin hx
  have he : (fun x => ‖f x‖) =ᵐ[volume.restrict V] (fun x => min ‖f x‖ M) :=
    hb.mono fun x hx => (min_eq_left hx).symm
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq he hV hf.norm.continuousOn
    (hf.norm.min continuous_const).continuousOn
  intro x hx
  exact (heq hx).trans_le (min_le_right _ _)

/-- The blueprint stability estimate with the actual derivative sup norms and
actual local essential supremum norm. No geometric containment is implicit:
every interpolated inverse image of `K` is required to lie in `V`. -/
theorem field_stability_compactlySupported
    {X Y : AmbientSpace → AmbientSpace}
    (hXC : ContDiff ℝ 1 X) (hXc : HasCompactSupport X)
    (hYC : ContDiff ℝ 1 Y) (hYc : HasCompactSupport Y) {t : ℝ}
    (ht : |t| * max ‖straightDerivativeField hXC hXc‖
      ‖straightDerivativeField hYC hYc‖ < 1 / 2)
    {K V U : Set AmbientSpace} (hK : MeasurableSet K)
    (hV : IsOpen V) (hU : IsOpen U) (hVU : V ⊆ U)
    {u : AmbientSpace → ℝ} (hu : IsBVOn u U)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V) :
    (∫ z in K, |u (invFun (straightPerturbation X t) z) -
      u (invFun (straightPerturbation Y t) z)|) ≤
      (16 * |t| * (eLpNorm (fun x => X x - Y x) ∞ (volume.restrict V)).toReal) *
        (variation u V).toReal := by
  let L : ℝ≥0 := max ‖straightDerivativeField hXC hXc‖₊
    ‖straightDerivativeField hYC hYc‖₊
  have hX : LipschitzWith L X := (lipschitzWith_straightDerivativeField hXC hXc).weaken
    (le_max_left _ _)
  have hY : LipschitzWith L Y := (lipschitzWith_straightDerivativeField hYC hYc).weaken
    (le_max_right _ _)
  have ht' : |t| * L < 1 / 2 := by simpa only [L, NNReal.coe_max, coe_nnnorm] using ht
  have hfc : HasCompactSupport (fun x => X x - Y x) := hXc.sub hYc
  have hfcont : Continuous (fun x => X x - Y x) := hXC.continuous.sub hYC.continuous
  obtain ⟨B, hB⟩ := hfc.exists_bound_of_continuous hfcont
  have hfbound : ∀ᵐ x ∂volume.restrict V, ‖X x - Y x‖ ≤ B :=
    Eventually.of_forall hB
  have hfin : eLpNormEssSup (fun x => X x - Y x) (volume.restrict V) ≠ ∞ :=
    (eLpNormEssSup_lt_top_of_ae_bound hfbound).ne
  have h := field_stability_on hX hY hXC hYC ht' hK hV hU hVU hu hpath
    (M := (eLpNormEssSup (fun x => X x - Y x) (volume.restrict V)).toReal)
    ENNReal.toReal_nonneg (norm_le_eLpNormEssSup_on_open
      (hXC.continuous.sub hYC.continuous) hV hfin)
  have he : eLpNorm (fun x => X x - Y x) ∞ (volume.restrict V) =
      eLpNormEssSup (fun x => X x - Y x) (volume.restrict V) :=
    eLpNorm_exponent_top (hXC.continuous.sub hYC.continuous).aestronglyMeasurable
  rw [he]
  simpa only [interpolatedInverse, interpolatedField_one, interpolatedField_zero] using h

/-- Composition with an interpolated inverse preserves local L¹ on every
measurable set mapped into an integrability domain. -/
lemma integrableOn_comp_interpolatedInverse
    {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y) {t s : ℝ}
    (ht : |t| * L < 1) (hs : s ∈ Icc 0 1) {K V : Set AmbientSpace}
    (hK : MeasurableSet K)
    (hmaps : MapsTo (interpolatedInverse X Y t s) K V)
    {u : AmbientSpace → ℝ} (hu : IntegrableOn u V) :
    IntegrableOn (u ∘ interpolatedInverse X Y t s) K := by
  let e := straightPerturbationHomeomorph (lipschitzWith_interpolatedField_Icc hX hY hs) ht
  have he : interpolatedInverse X Y t s = e.symm :=
    interpolatedInverse_eq_homeomorph hX hY ht hs
  rw [he]
  exact integrableOn_comp_of_lipschitz_leftInverse hK e.symm.continuous.continuousOn
    (lipschitzWith_straightPerturbation
      (lipschitzWith_interpolatedField_Icc hX hY hs) t).lipschitzOnWith
    (he ▸ hmaps) (fun z _ => e.apply_symm_apply z) hu

/-- Nonnegative - integral form, with the actual extended - real variation. -/
theorem lintegral_field_stability {X Y : AmbientSpace → AmbientSpace} {L : ℝ≥0}
    (hX : LipschitzWith L X) (hY : LipschitzWith L Y)
    (hXC : ContDiff ℝ 1 X) (hYC : ContDiff ℝ 1 Y) {t : ℝ}
    (ht : |t| * L < 1 / 2) {K V : Set AmbientSpace}
    (hK : MeasurableSet K) (hV : IsOpen V)
    {u : AmbientSpace → ℝ} (hu : IsBVOn u V)
    (hpath : ∀ s ∈ Icc (0 : ℝ) 1, MapsTo (interpolatedInverse X Y t s) K V)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ V, ‖X x - Y x‖ ≤ M) :
    (∫⁻ z in K, ‖u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)‖ₑ) ≤
      ENNReal.ofReal (16 * |t| * M) * variation u V := by
  have ht1 : |t| * L < 1 := lt_trans ht (by norm_num)
  have hiq (s : ℝ) (hs : s ∈ Icc 0 1) :=
    integrableOn_comp_interpolatedInverse hX hY ht1 hs hK (hpath s hs) hu.1
  have hi : IntegrableOn (fun z => u (interpolatedInverse X Y t 1 z) -
      u (interpolatedInverse X Y t 0 z)) K := (hiq 1 (by simp)).sub (hiq 0 (by simp))
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  have h := ENNReal.ofReal_le_ofReal (field_stability hX hY hXC hYC ht hK hV hu hpath hM hbound)
  simpa only [Real.norm_eq_abs, ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * |t| * M),
    ENNReal.ofReal_toReal hu.2.ne] using h

end LiquidDrop
