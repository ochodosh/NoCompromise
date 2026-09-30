module

public import NoCompromise.Elliptic.BoundaryHolderTests
public import NoCompromise.Sobolev.H1FlatExtension

@[expose] public section

/-!
# Localized actual flat trace

The existing normal-average trace is applied after a cutoff supported inside
the ambient neighborhood. It uses only the upper-halfspace data. Its vanishing
is the local zero Dirichlet trace convention, independently of any zero-extension
or H¹₀ conclusion.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual flat trace after multiplying by a compactly supported cutoff. -/
def boundaryLocalizedFlatTrace {k : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  flatTraceFunction (fun x => ζ x * f x) (fun x => ζ x • G x + f x • gradient ζ x)

/-- Vanishing of the actual localized flat trace in an ambient open neighborhood.
Only upper-halfspace values of the function and its weak gradient enter this condition. -/
def HasZeroFlatTraceOn {k : ℕ}
    (f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1)))
    (W : Set (EuclideanSpace ℝ (Fin (k + 1)))) : Prop :=
  ∀ ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ →
    HasCompactSupport ζ → tsupport ζ ⊆ W →
      boundaryLocalizedFlatTrace f G ζ =ᵐ[volume] 0

lemma boundary_cutoff_data_congr_ae_upper {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f g ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hsζ : tsupport ζ ⊆ W)
    (hfg : f =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] g)
    (hGH : G =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] H) :
    (fun x => ζ x * f x) =ᵐ[volume.restrict {x | 0 < x (Fin.last k)}]
      (fun x => ζ x * g x) ∧
    (fun x => ζ x • G x + f x • gradient ζ x) =ᵐ[
        volume.restrict {x | 0 < x (Fin.last k)}]
      (fun x => ζ x • H x + g x • gradient ζ x) := by
  have hU := (boundary_holder_open_upper (k := k)).measurableSet
  have hf := (ae_restrict_iff' (hW.inter hU)).mp hfg
  have hG := (ae_restrict_iff' (hW.inter hU)).mp hGH
  have hz (x) (hx : x ∉ W) : ζ x = 0 ∧ gradient ζ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht)),
      gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht))⟩
  constructor
  · filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem hU] with x hx hxu
    by_cases hxW : x ∈ W
    · rw [hx ⟨hxW, hxu⟩]
    · rw [(hz x hxW).1, zero_mul, zero_mul]
  · filter_upwards [ae_restrict_of_ae hf, ae_restrict_of_ae hG,
      ae_restrict_mem hU] with x hx hy hxu
    by_cases hxW : x ∈ W
    · rw [hx ⟨hxW, hxu⟩, hy ⟨hxW, hxu⟩]
    · simp only [(hz x hxW).1, (hz x hxW).2, zero_smul, smul_zero]

/-- The localized trace is independent of almost-everywhere representatives and
of all values outside the upper part of the localization neighborhood. -/
lemma boundaryLocalizedFlatTrace_congr_ae {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f g ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hsζ : tsupport ζ ⊆ W)
    (hfg : f =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] g)
    (hGH : G =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] H) :
    boundaryLocalizedFlatTrace f G ζ =ᵐ[volume] boundaryLocalizedFlatTrace g H ζ := by
  obtain ⟨hf, hG⟩ := boundary_cutoff_data_congr_ae_upper hW hsζ hfg hGH
  apply flatTraceFunction_congr_ae_on_slab
  · exact ae_mono (Measure.restrict_mono (fun _ hx => hx.1) le_rfl) hf
  · exact ae_mono (Measure.restrict_mono (fun _ hx => hx.1) le_rfl) hG

lemma HasZeroFlatTraceOn.congr_ae {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hW : MeasurableSet W)
    {f g : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G H : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasZeroFlatTraceOn f G W)
    (hfg : f =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] g)
    (hGH : G =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last k)})] H) :
    HasZeroFlatTraceOn g H W := by
  intro ζ hζ hcζ hsζ
  exact (boundaryLocalizedFlatTrace_congr_ae hW hsζ hfg hGH).symm.trans (hf ζ hζ hcζ hsζ)

/-- For smooth functions this convention is exactly classical boundary restriction. -/
lemma boundaryLocalizedFlatTrace_eq_restrict {k : ℕ}
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hf : ContDiff ℝ 1 f) (hζ : ContDiff ℝ 1 ζ) (x : EuclideanSpace ℝ (Fin k)) :
    boundaryLocalizedFlatTrace f (gradient f) ζ x =
      ζ (graphAppendN x 0) * f (graphAppendN x 0) := by
  have he : (fun y => ζ y • gradient f y + f y • gradient ζ y) =
      gradient (fun y => ζ y * f y) := by
    ext y i
    rw [gradient_mul hζ hf]
  rw [boundaryLocalizedFlatTrace, he, flatTraceFunction_eq_restrict_of_contDiff (hζ.mul hf)]

lemma HasZeroFlatTraceOn.mono {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {U W : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hf : HasZeroFlatTraceOn f G W) (hUW : U ⊆ W) : HasZeroFlatTraceOn f G U :=
  fun ζ hζ hcζ hsζ => hf ζ hζ hcζ (hsζ.trans hUW)

lemma hasZeroFlatTraceOn_of_contDiff {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hf : ContDiff ℝ 1 f)
    (hz : ∀ x : EuclideanSpace ℝ (Fin k), graphAppendN x 0 ∈ W →
      f (graphAppendN x 0) = 0) : HasZeroFlatTraceOn f (gradient f) W := by
  intro ζ hζ _ hsζ
  apply Eventually.of_forall
  intro x
  change boundaryLocalizedFlatTrace f (gradient f) ζ x = 0
  rw [boundaryLocalizedFlatTrace_eq_restrict hf (hζ.of_le (by simp))]
  by_cases hx : graphAppendN x 0 ∈ W
  · rw [hz x hx, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsζ ht)), zero_mul]

/-- Actual zero trace yields an actual global H¹ zero extension after localization
inside a half-cube. Even reflection supplies the auxiliary extension, and weak
-gradient uniqueness identifies its gradient on the original upper domain. -/
theorem HasH1GradientOn.boundary_zero_extension_halfCube {k : ℕ}
    {R r : ℝ} (hrR : r < R)
    {f ζ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G (coordinateHalfCube (Fin.last k) R))
    (hT : HasZeroFlatTraceOn f G (coordinateCube (k + 1) R))
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ coordinateCube (k + 1) r) :
    HasH1GradientOn
      ({x | 0 < x (Fin.last k)}.indicator (fun x => ζ x * f x))
      ({x | 0 < x (Fin.last k)}.indicator
        (fun x => ζ x • G x + f x • gradient ζ x)) univ := by
  let U := {x : EuclideanSpace ℝ (Fin (k + 1)) | 0 < x (Fin.last k)}
  have hU : IsOpen U := boundary_holder_open_upper
  obtain ⟨H, hH, _, _⟩ := hf.coordinateFold_halfCube (Fin.last k) hrR
  have hsub : coordinateHalfCube (Fin.last k) r ⊆ coordinateHalfCube (Fin.last k) R :=
    inter_subset_inter_left _ (coordinateCube_mono hrR.le)
  have hfg : (f ∘ coordinateFold (Fin.last k)) =ᵐ[
      volume.restrict (coordinateHalfCube (Fin.last k) r)] f := by
    filter_upwards [ae_restrict_mem (isOpen_coordinateHalfCube (Fin.last k) r).measurableSet]
      with x hx
    simp only [Function.comp_def, coordinateFold_eq_self hx.2.le]
  have hHupper := (hH.mono inter_subset_left).congr_ae hfg EventuallyEq.rfl
  have hHG : H =ᵐ[volume.restrict (coordinateHalfCube (Fin.last k) r)] G :=
    HasWeakGradientOn.unique (isOpen_coordinateHalfCube (Fin.last k) r)
      hHupper.toHasWeakGradientOn (hf.mono hsub).toHasWeakGradientOn
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hc := hH.locallyH1.mul_compact_cutoff hζ1 hcζ hsζ
  have htc : flatTraceFunction (fun x => ζ x * (f ∘ coordinateFold (Fin.last k)) x)
      (fun x => ζ x • H x + (f ∘ coordinateFold (Fin.last k)) x • gradient ζ x)
        =ᵐ[volume] 0 :=
    (boundaryLocalizedFlatTrace_congr_ae (isOpen_coordinateCube (k + 1) r).measurableSet
      hsζ hfg hHG).trans
        (hT ζ hζ hcζ (hsζ.trans (coordinateCube_mono hrR.le)))
  have hzero := hc.indicator_upperHalfspace_of_flatTrace_zero htc
  have hdata := boundary_cutoff_data_congr_ae_upper
    (isOpen_coordinateCube (k + 1) r).measurableSet hsζ hfg hHG
  have hfglobal : U.indicator (fun x => ζ x * (f ∘ coordinateFold (Fin.last k)) x)
      =ᵐ[volume] U.indicator (fun x => ζ x * f x) :=
    by
      filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hdata.1] with x hx
      by_cases hxU : x ∈ U <;> simp only [indicator_apply, hxU, ↓reduceIte]
      exact hx hxU
  have hGglobal : U.indicator
      (fun x => ζ x • H x + (f ∘ coordinateFold (Fin.last k)) x • gradient ζ x)
      =ᵐ[volume] U.indicator (fun x => ζ x • G x + f x • gradient ζ x) :=
    by
      filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hdata.2] with x hx
      by_cases hxU : x ∈ U <;> simp only [indicator_apply, hxU, ↓reduceIte]
      exact hx hxU
  exact hzero.congr_ae (by simpa only [Measure.restrict_univ, smoothEpigraph] using hfglobal)
    (by simpa only [Measure.restrict_univ, smoothEpigraph] using hGglobal)

end LiquidDrop
