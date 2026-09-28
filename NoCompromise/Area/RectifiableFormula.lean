import NoCompromise.Area.Rectifiable
import NoCompromise.Area.TangentAlgebra

/-!
# The area formula on countably rectifiable sets, chartwise

For a fixed family of disjoint injective rank-two Lipschitz chart pieces, the tangent
plane at `x = f i z` is taken to be `range (fderiv ℝ (f i) z)`, and the tangential
Jacobian of `Φ` is the chart quotient `J₂(Φ ∘ f i)(z) / J₂(f i)(z)`. This is the
norm determinant of `chartTangentialMap`. No intrinsic approximate tangent plane is
used. The weighted area formula with fiber sums then holds for every Borel weight.
-/

noncomputable section
open MeasureTheory Set Function
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
/-- The chartwise tangential Jacobian: `J₂(Φ ∘ f i)(z) / J₂(f i)(z)` at `x = f i z`
with `z ∈ A i`, and `0` off the chart pieces. -/
noncomputable def chartTangentialJacobian (Φ : E3 → E3) (f : ℕ → E2 → E3)
    (A : ℕ → Set E2) (x : E3) : ℝ :=
  if h : ∃ p : ℕ × E2, p.2 ∈ A p.1 ∧ f p.1 p.2 = x then
    jacobian2 (Φ ∘ f h.choose.1) h.choose.2 / jacobian2 (f h.choose.1) h.choose.2
  else 0

/-- Disjoint injective pieces determine the chart parameter of a covered point. -/
lemma chart_parameter_unique {f : ℕ → E2 → E3} {A : ℕ → Set E2}
    (hinj : ∀ i, InjOn (f i) (A i)) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {i j : ℕ} {z w : E2} (hz : z ∈ A i) (hw : w ∈ A j) (hfw : f j w = f i z) :
    j = i ∧ w = z := by
  have hji : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) ⟨w, hw, rfl⟩ ⟨z, hz, hfw.symm⟩
  subst hji
  exact ⟨rfl, hinj j hw hz hfw⟩

/-- Evaluation of the chartwise tangential Jacobian on a chart piece. -/
theorem chartTangentialJacobian_apply (Φ : E3 → E3) {f : ℕ → E2 → E3} {A : ℕ → Set E2}
    (hinj : ∀ i, InjOn (f i) (A i)) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {i : ℕ} {z : E2} (hz : z ∈ A i) :
    chartTangentialJacobian Φ f A (f i z) = jacobian2 (Φ ∘ f i) z / jacobian2 (f i) z := by
  have h : ∃ p : ℕ × E2, p.2 ∈ A p.1 ∧ f p.1 p.2 = f i z := ⟨(i, z), hz, rfl⟩
  rw [chartTangentialJacobian, dif_pos h]
  obtain ⟨hw, hfw⟩ := h.choose_spec
  obtain ⟨h1, h2⟩ := chart_parameter_unique hinj hd hz hw hfw
  have hp : h.choose = (i, z) := Prod.ext h1 h2
  rw [hp]

/-- The chartwise tangential Jacobian is the norm determinant of the tangential
differential `D^S Φ(x)`, the unique map on the chart range with
`D^S Φ(x) ∘ D(f i)(z) = D(Φ ∘ f i)(z)`. -/
theorem chartTangentialJacobian_eq_normDet (Φ : E3 → E3) {f : ℕ → E2 → E3}
    {A : ℕ → Set E2}
    (hinj : ∀ i, InjOn (f i) (A i)) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {i : ℕ} {z : E2} (hz : z ∈ A i) (hK : Function.Injective (fderiv ℝ (f i) z)) :
    chartTangentialJacobian Φ f A (f i z) =
      (chartTangentialMap (fderiv ℝ (f i) z) hK (fderiv ℝ (Φ ∘ f i) z)).normDet := by
  rw [chartTangentialJacobian_apply Φ hinj hd hz, jacobian2, jacobian2,
    chartTangentialMap_jacobian_factor (fderiv ℝ (f i) z) hK (fderiv ℝ (Φ ∘ f i) z),
    mul_div_assoc, div_self (ne_of_gt ((jacobian2Linear_pos_iff_injective _).mpr hK)),
    mul_one]

/-- The same identity in any orthonormal coordinates on the chart range. -/
theorem chartTangentialJacobian_eq_jacobian2Linear (Φ : E3 → E3) {f : ℕ → E2 → E3}
    {A : ℕ → Set E2}
    (hinj : ∀ i, InjOn (f i) (A i)) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {i : ℕ} {z : E2} (hz : z ∈ A i) (hK : Function.Injective (fderiv ℝ (f i) z))
    (e : E2 ≃ₗᵢ[ℝ] (fderiv ℝ (f i) z).range) :
    chartTangentialJacobian Φ f A (f i z) =
      jacobian2Linear ((chartTangentialMap (fderiv ℝ (f i) z) hK (fderiv ℝ (Φ ∘ f i) z)).comp
        e.toContinuousLinearEquiv.toContinuousLinearMap) := by
  rw [chartTangentialMap_jacobian_quotient, chartTangentialJacobian_apply Φ hinj hd hz]
  rfl

/-- Chain rule: for `Φ` differentiable at `f i z`, the chart tangential differential is
the restriction of `DΦ(f i z)` to the chart range. -/
theorem chartTangentialMap_eq_fderiv_comp_subtypeL {Φ : E3 → E3} {g : E2 → E3} {z : E2}
    (hg : DifferentiableAt ℝ g z) (hK : Function.Injective (fderiv ℝ g z))
    (hΦ : DifferentiableAt ℝ Φ (g z)) :
    chartTangentialMap (fderiv ℝ g z) hK (fderiv ℝ (Φ ∘ g) z) =
      (fderiv ℝ Φ (g z)).comp (fderiv ℝ g z).range.subtypeL := by
  symm
  apply chartTangentialMap_unique
  rw [fderiv_comp z hΦ hg]
  exact ContinuousLinearMap.ext fun _ => rfl

/-- A restricted chart is a measurable embedding of its Borel uniform piece. -/
lemma measurableEmbedding_piece_restrict {f : E2 → E3} {A : Set E2} (hf : Measurable f)
    (hA : IsUniformDifferentiabilityPiece f A) (hinj : InjOn f A) :
    MeasurableEmbedding (fun x : A => f x) := by
  refine ⟨fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy), hf.comp measurable_subtype_coe, ?_⟩
  intro s hs
  have he : (fun x : A => f x) '' s = f '' (Subtype.val '' s) := by
    rw [← image_comp]
    rfl
  rw [he]
  exact (hA.mono (hA.1.subtype_image hs) (Subtype.coe_image_subset _ _)).measurableSet_image

/-- Pushforward integrals along an injective chart piece need no measurability of the
integrand. -/
lemma lintegral_map_piece {f : E2 → E3} {A : Set E2} (hf : Measurable f)
    (hA : IsUniformDifferentiabilityPiece f A) (hinj : InjOn f A) (μ : Measure E2)
    (g : E3 → ℝ≥0∞) :
    ∫⁻ x, g x ∂(Measure.map f (μ.restrict A)) = ∫⁻ z in A, g (f z) ∂μ := by
  rw [← map_comap_subtype_coe hA.1 μ, Measure.map_map hf measurable_subtype_coe,
    show f ∘ (Subtype.val : A → E2) = fun x : A => f x from rfl,
    (measurableEmbedding_piece_restrict hf hA hinj).lintegral_map,
    lintegral_subtype_comap hA.1 (fun z => g (f z)), map_comap_subtype_coe hA.1 μ]

/-- One chart piece of the weighted area integral. -/
lemma lintegral_chart_piece {Φ : E3 → E3} {f : ℕ → E2 → E3} {A : ℕ → Set E2}
    (hf : ∀ i, Measurable (f i)) (hA : ∀ i, IsUniformDifferentiabilityPiece (f i) (A i))
    (hinj : ∀ i, InjOn (f i) (A i)) (hrank : ∀ i, A i ⊆ rankTwoDifferentiabilitySet (f i))
    (hd : Pairwise (Disjoint on fun i => f i '' A i))
    {q : E3 → ℝ≥0∞} (hq : Measurable q) (i : ℕ) :
    (∫⁻ x, q x * ENNReal.ofReal (chartTangentialJacobian Φ f A x) ∂(Measure.map (f i)
        ((volume.restrict (A i)).withDensity
          (fun x => ENNReal.ofReal (jacobian2 (f i) x))))) =
      ∫⁻ z in A i, (q ∘ f i) z * ENNReal.ofReal (jacobian2 (Φ ∘ f i) z) := by
  have hm := (hA i).1
  rw [← restrict_withDensity hm, lintegral_map_piece (hf i) (hA i) (hinj i)]
  rw [setLIntegral_congr_fun hm (g := fun z => q (f i z) *
      ENNReal.ofReal (jacobian2 (Φ ∘ f i) z / jacobian2 (f i) z))
    (fun z hz => by rw [chartTangentialJacobian_apply Φ hinj hd hz])]
  refine (setLIntegral_withDensity_eq_setLIntegral_mul volume
    (f := fun x => ENNReal.ofReal (jacobian2 (f i) x))
    (g := fun z => q (f i z) * ENNReal.ofReal (jacobian2 (Φ ∘ f i) z / jacobian2 (f i) z))
    (measurable_jacobian2 _).ennreal_ofReal
    ((hq.comp (hf i)).mul
      ((measurable_jacobian2 _).div (measurable_jacobian2 _)).ennreal_ofReal) hm).trans ?_
  apply setLIntegral_congr_fun hm
  intro z hz
  have hpos : 0 < jacobian2 (f i) z :=
    (jacobian2Linear_pos_iff_injective _).mpr (hrank i hz).2
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [mul_left_comm, ← ENNReal.ofReal_mul hpos.le, mul_div_cancel₀ _ hpos.ne']

/-- Fibers of `Φ` over an injective image are fibers of the composite chart. -/
lemma areaMultiplicity_image_of_injOn {α β γ : Type*} {g : α → β} {Φ : β → γ} {A : Set α}
    (hg : InjOn g A) (q : β → ℝ≥0∞) (y : γ) :
    areaMultiplicity Φ (g '' A) q y = areaMultiplicity (Φ ∘ g) A (q ∘ g) y := by
  rw [areaMultiplicity_eq_tsum_fiber, areaMultiplicity_eq_tsum_fiber]
  have he : g '' A ∩ Φ ⁻¹' {y} = g '' (A ∩ (Φ ∘ g) ⁻¹' {y}) := by
    rw [preimage_comp, image_inter_preimage]
  rw [he]
  exact tsum_image q (hg.mono inter_subset_left)

/-- Blueprint `thm:area-formula-rect`, chartwise tangent convention: for a fixed family of
disjoint injective rank-two Lipschitz chart pieces covering `S` up to a null set, the
weighted area formula holds with the chartwise tangential Jacobian. -/
theorem area_formula_rect_chartwise {S : Set E3} {Φ : E3 → E3} {LΦ : ℝ≥0}
    (hΦ : LipschitzWith LΦ Φ)
    (f : ℕ → E2 → E3) (L : ℕ → ℝ≥0) (A : ℕ → Set E2)
    (hf : ∀ i, LipschitzWith (L i) (f i)) (hA : ∀ i, IsUniformDifferentiabilityPiece (f i) (A i))
    (hinj : ∀ i, InjOn (f i) (A i)) (hrank : ∀ i, A i ⊆ rankTwoDifferentiabilitySet (f i))
    (hAS : ∀ i, f i '' A i ⊆ S) (hd : Pairwise (Disjoint on fun i => f i '' A i))
    (hn : hausdorffMeasure2 3 (S \ ⋃ i, f i '' A i) = 0)
    {q : E3 → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ x in S, q x * ENNReal.ofReal (chartTangentialJacobian Φ f A x) ∂hausdorffMeasure2 3) =
      ∫⁻ y, ∑' x : ↥(S ∩ Φ ⁻¹' {y}), q x ∂hausdorffMeasure2 3 := by
  have hfm (i : ℕ) : Measurable (f i) := (hf i).continuous.measurable
  let C := ⋃ i, f i '' A i
  have hCS : C ⊆ S := iUnion_subset hAS
  have hnullΦ : hausdorffMeasure2 3 (Φ '' (S \ C)) = 0 :=
    hausdorffMeasure2_image_null_of_lipschitz hΦ hn
  rw [hausdorffMeasure2_restrict_eq_sum_chart_maps f A hfm hA hinj hAS hd hn,
    lintegral_sum_measure]
  calc
    _ = ∑' i, ∫⁻ z in A i, (q ∘ f i) z * ENNReal.ofReal (jacobian2 (Φ ∘ f i) z) :=
      tsum_congr fun i => lintegral_chart_piece hfm hA hinj hrank hd hq i
    _ = ∑' i, ∫⁻ y, areaMultiplicity (Φ ∘ f i) (A i) (q ∘ f i) y ∂hausdorffMeasure2 3 :=
      tsum_congr fun i =>
        area_formula_two_dimensional (hΦ.comp (hf i)) (hA i).1 (hq.comp (hfm i))
    _ = ∫⁻ y, ∑' i, areaMultiplicity (Φ ∘ f i) (A i) (q ∘ f i) y ∂hausdorffMeasure2 3 :=
      (lintegral_tsum fun i => aemeasurable_areaMultiplicity_lipschitz_planar
        (hΦ.comp (hf i)) (hA i).1 (hq.comp (hfm i))).symm
    _ = ∫⁻ y, areaMultiplicity Φ C q y ∂hausdorffMeasure2 3 := by
      apply lintegral_congr
      intro y
      rw [areaMultiplicity_iUnion Φ (fun i => f i '' A i) hd q y]
      exact tsum_congr fun i => (areaMultiplicity_image_of_injOn (hinj i) q y).symm
    _ = ∫⁻ y, areaMultiplicity Φ S q y ∂hausdorffMeasure2 3 := by
      apply lintegral_congr_ae
      filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnullΦ] with y hy
      rw [areaMultiplicity_inter_of_notMem_image_sdiff q hy, inter_eq_right.mpr hCS]
    _ = _ := by
      simp only [areaMultiplicity_eq_tsum_fiber]

/-- Blueprint `thm:area-formula-rect`, chartwise tangent convention: every countably
rectifiable set has disjoint injective rank-two Lipschitz chart pieces for which the
weighted area formula holds for every Lipschitz `Φ` and every Borel weight. -/
theorem CountablyH2Rectifiable.area_formula_rect_chartwise {S : Set E3}
    (hS : CountablyH2Rectifiable S) :
    ∃ (f : ℕ → E2 → E3) (L : ℕ → ℝ≥0) (A : ℕ → Set E2),
      (∀ i, LipschitzWith (L i) (f i)) ∧
      (∀ i, IsUniformDifferentiabilityPiece (f i) (A i)) ∧
      (∀ i, InjOn (f i) (A i)) ∧
      (∀ i, A i ⊆ rankTwoDifferentiabilitySet (f i)) ∧
      (∀ i, f i '' A i ⊆ S) ∧
      Pairwise (Disjoint on fun i => f i '' A i) ∧
      hausdorffMeasure2 3 (S \ ⋃ i, f i '' A i) = 0 ∧
      ∀ (Φ : E3 → E3) (LΦ : ℝ≥0), LipschitzWith LΦ Φ →
        ∀ q : E3 → ℝ≥0∞, Measurable q →
          (∫⁻ x in S, q x * ENNReal.ofReal (chartTangentialJacobian Φ f A x)
              ∂hausdorffMeasure2 3) =
            ∫⁻ y, ∑' x : ↥(S ∩ Φ ⁻¹' {y}), q x ∂hausdorffMeasure2 3 := by
  obtain ⟨f, L, A, hf, hA, hinj, hrank, hAS, hd, hn⟩ := hS.exists_injective_chart_pieces
  exact ⟨f, L, A, hf, hA, hinj, hrank, hAS, hd, hn, fun Φ _ hΦ q hq =>
    LiquidDrop.area_formula_rect_chartwise hΦ f L A hf hA hinj hrank hAS hd hn hq⟩

end LiquidDrop
