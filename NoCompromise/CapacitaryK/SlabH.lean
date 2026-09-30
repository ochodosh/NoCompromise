module

public import NoCompromise.CapacitaryK.SlabGaussGreen
public import NoCompromise.CapacitaryK.PushforwardDensity
public import NoCompromise.CapacitaryK.HarmonicSmooth
public import NoCompromise.CapacitaryK.SlabCoarea

@[expose] public section

/-!
# The two slab identities from Gauss-Green on the slab (chapter 31)

With `hGG` the Gauss-Green formula on the regular slab `S = U ∩ {a < u < b}` (proved as
`slab_gauss_green`):

* `K_slab_H_of_gauss_green` (`lem:K-slab-H`): `μ(S) = ∫_{u=b} Hw - ∫_{u=a} Hw`. Route: a smooth
  `φ = χ(u)` equal to `1` near the compact critical set of `closure S` and supported in `S`; the
  field `(1 - φ)∇w + w∇φ` is `C¹` near `closure S` (it vanishes near the critical set), has
  divergence `(1 - φ)Δw + wΔφ`, and its total integral is `μ(S)` because `μ = Δw dx` where
  `1 - φ ≠ 0` and `∫ wΔφ = ∫ φ dμ`. No `ε`-regularisation is needed.
* `K_slab_F_gauss_green_of_gauss_green` (Gauss-Green half of `lem:K-slab-F`):
  `F(b) - F(a) = ∫_S ∇w·∇u`, applying `hGG` to `w∇u = N(∇u)` with `N(v) = ‖v‖v` of class `C¹`.
-/

noncomputable section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace ENNReal ContDiff

namespace LiquidDrop.CapacitaryK

private lemma slab_contDiffAt_gradient {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (gradient f) x :=
  (toDual ℝ E3).symm.contDiff.contDiffAt.comp x (hf.fderiv_right (by norm_num))

private lemma slab_vecDiv_gradient {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) : vecDiv (gradient f) x = laplacianN f x := by
  classical
  unfold vecDiv laplacianN
  apply Finset.sum_congr rfl
  intro i _
  have hd := (slab_contDiffAt_gradient hf).differentiableAt one_ne_zero
  have he : (fun y => gradient f y i) = poissonCoordinateDerivative i f := by
    funext y
    exact (poissonCoordinateDerivative_eq_gradient i f y).symm
  rw [← he]
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  exact (congrArg (fun L : E3 →L[ℝ] ℝ => L (basisVec i)) hh).symm

private lemma slab_vecDiv_smul_gradient {f g : E3 → ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : ContDiffAt ℝ 2 g x) :
    vecDiv (fun y => f y • gradient g y) x =
      ⟪gradient f x, gradient g x⟫ + f x * laplacianN g x := by
  classical
  have hd := (slab_contDiffAt_gradient hg).differentiableAt one_ne_zero
  rw [← slab_vecDiv_gradient hg]
  have he := (hf.hasFDerivAt.smul hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y • gradient g y) x = _ at he
  simp only [vecDiv, he, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← gradient_apply_eq_fderiv_basisVec]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, mul_comm]
  ring

private lemma slab_vecDiv_add {X Y : E3 → E3} {x : E3}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    vecDiv (fun y => X y + Y y) x = vecDiv X x + vecDiv Y x := by
  simp only [vecDiv, fderiv_fun_add hX hY, add_apply,
    PiLp.add_apply, Finset.sum_add_distrib]

private lemma slab_cutoff_field_near_one {w φ : E3 → ℝ} {x : E3}
    (h : φ =ᶠ[𝓝 x] (fun _ => 1)) :
    (fun y => (1 - φ y) • gradient w y + w y • gradient φ y) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [h, h.gradient] with y hy hgy
  simp only [hy, hgy, gradient_fun_const, sub_self, zero_smul, smul_zero, add_zero]

private lemma slab_cutoff_field_contDiffAt {w φ : E3 → ℝ} {x : E3}
    (hw : ContDiffAt ℝ 2 w x) (hφ : ContDiffAt ℝ 2 φ x) :
    ContDiffAt ℝ 1 (fun y => (1 - φ y) • gradient w y + w y • gradient φ y) x :=
  ((contDiffAt_const.sub (hφ.of_le (by norm_num))).smul
    (slab_contDiffAt_gradient hw)).add
      ((hw.of_le (by norm_num)).smul (slab_contDiffAt_gradient hφ))

private lemma slab_cutoff_field_div {w φ : E3 → ℝ} {x : E3}
    (hw : ContDiffAt ℝ 2 w x) (hφ : ContDiffAt ℝ 2 φ x) :
    vecDiv (fun y => (1 - φ y) • gradient w y + w y • gradient φ y) x =
      (1 - φ x) * laplacianN w x + w x * laplacianN φ x := by
  have hw' := hw.differentiableAt (by norm_num)
  have hφ' := hφ.differentiableAt (by norm_num)
  rw [slab_vecDiv_add (X := fun y => (1 - φ y) • gradient w y)
    (Y := fun y => w y • gradient φ y)
    (((differentiableAt_const (1 : ℝ)).sub hφ').smul
      ((slab_contDiffAt_gradient hw).differentiableAt one_ne_zero))
    (hw'.smul ((slab_contDiffAt_gradient hφ).differentiableAt one_ne_zero)),
    slab_vecDiv_smul_gradient (f := fun y => 1 - φ y)
      ((differentiableAt_const (1 : ℝ)).sub hφ') hw,
    slab_vecDiv_smul_gradient hw' hφ]
  have he : gradient (fun y => 1 - φ y) x = -gradient φ x := by
    simp only [gradient, fderiv_fun_sub (differentiableAt_const _) hφ',
      fderiv_fun_const, Pi.zero_apply, zero_sub, map_neg]
  rw [he, inner_neg_left, real_inner_comm (gradient w x) (gradient φ x)]
  ring

/-- A cutoff supported in the slab and equal to one near every critical point in its
closure. Regularity of the two boundary values is used only to keep this critical set
inside the open slab. -/
private lemma slab_critical_cutoff {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {a b : ℝ} (hab : a < b)
    (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    ∃ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ U ∩ u ⁻¹' Ioo a b ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      ∀ x ∈ closure (U ∩ u ⁻¹' Ioo a b), gradient u x = 0 →
        φ =ᶠ[𝓝 x] (fun _ => 1) := by
  let S := U ∩ u ⁻¹' Ioo a b
  have hS : IsOpen S := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo
  have hK : IsCompact (closure S) := hbdd.isCompact_closure
  have hgrad : ContinuousOn (gradient u) (closure S) := by
    intro x hx
    exact (slab_contDiffAt_gradient
      ((hu.contDiffAt (hU.mem_nhds (hcl hx))).of_le (by norm_num))).continuousAt.continuousWithinAt
  have hZ : IsCompact (closure S ∩ gradient u ⁻¹' {0}) :=
    hK.of_isClosed_subset (hgrad.preimage_isClosed_of_isClosed isClosed_closure
      isClosed_singleton) inter_subset_left
  have hZS : closure S ∩ gradient u ⁻¹' {0} ⊆ S := by
    rintro x ⟨hx, hx0⟩
    have hmap : MapsTo u S (Ioo a b) := fun _ hy => hy.2
    have hi := hmap.closure_of_continuousOn (hu.continuousOn.mono hcl) hx
    rw [closure_Ioo hab.ne] at hi
    exact ⟨hcl hx, lt_of_le_of_ne hi.1 (fun he => hreg x (hcl hx) (Or.inl he.symm) hx0),
      lt_of_le_of_ne hi.2 (fun he => hreg x (hcl hx) (Or.inr he) hx0)⟩
  obtain ⟨φ, hφ, hcφ, hsφ, hone, h01⟩ :=
    exists_smooth_cutoff_one_near_compact hZ hS hZS
  refine ⟨φ, hφ, hcφ, hsφ, h01, ?_⟩
  intro x hx hx0
  exact hone.filter_mono (nhds_le_nhdsSet
    (show x ∈ closure S ∩ gradient u ⁻¹' {0} from ⟨hx, hx0⟩))

private lemma slab_integral_regular_weight {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {S : Set E3} (hS : MeasurableSet S) {f : E3 → ℝ}
    (hz : ∀ x ∈ S, x ∉ U ∩ {x | 0 < gradNorm u x} → f x = 0) :
    (∫ x in S, f x ∂μ) = ∫ x in S, f x * laplacianN (gradNorm u) x := by
  let R := U ∩ {x | 0 < gradNorm u x}
  have hR : IsOpen R := isOpen_regularSet hU hu
  have hc := continuousOn_laplacianN_gradNorm_regular hR (hu.mono inter_subset_left)
    (fun _ hx => hx.2)
  have hnn (x) (hx : x ∈ R) : 0 ≤ laplacianN (gradNorm u) x := by
    apply laplacianN_gradNorm_nonneg_of_pos (hu.contDiffAt (hU.mem_nhds hx.1)) _ hx.2
    filter_upwards [hU.mem_nhds hx.1] with y hy
    exact hΔ y hy
  have hzero (x) (hx : x ∉ R) : S.indicator f x = 0 := by
    by_cases hs : x ∈ S
    · rw [indicator_of_mem hs, hz x hs hx]
    · exact indicator_of_notMem hs _
  calc
    _ = ∫ x in R, S.indicator f x ∂μ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_indicator hS]
    _ = ∫ x in R, laplacianN (gradNorm u) x * S.indicator f x := by
      rw [K_mu_restrict_regular hU hu hΔ hμK hμ]
      rw [integral_withDensity_eq_integral_toReal_smul₀
        ((hc.aestronglyMeasurable hR.measurableSet).aemeasurable.ennreal_ofReal)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hR.measurableSet] with x hx
      rw [ENNReal.toReal_ofReal (hnn x hx), smul_eq_mul]
    _ = ∫ x, laplacianN (gradNorm u) x * S.indicator f x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [hzero x hx, mul_zero]
    _ = _ := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ S <;> simp [hx, mul_comm]

/-- `lem:K-slab-H`, from Gauss-Green on the regular slab. -/
theorem K_slab_H_of_gauss_green {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {a b : ℝ} (hab : a < b) (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0)
    (hGG : ∀ {V : Set E3}, IsOpen V → closure (U ∩ u ⁻¹' Ioo a b) ⊆ V →
      ∀ {X : E3 → E3}, ContDiffOn ℝ 1 X V →
      ∫ x in U ∩ u ⁻¹' Ioo a b, vecDiv X x =
        (∫ x in U ∩ u ⁻¹' {b}, ⟪X x, gradient u x⟫ / gradNorm u x
            ∂(Measure.euclideanHausdorffMeasure 2)) -
          ∫ x in U ∩ u ⁻¹' {a}, ⟪X x, gradient u x⟫ / gradNorm u x
            ∂(Measure.euclideanHausdorffMeasure 2)) :
    (μ (U ∩ u ⁻¹' Ioo a b)).toReal =
      (∫ x in U ∩ u ⁻¹' {b}, meanCurv u x * gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)) -
        ∫ x in U ∩ u ⁻¹' {a}, meanCurv u x * gradNorm u x
          ∂(Measure.euclideanHausdorffMeasure 2) := by
  let S := U ∩ u ⁻¹' Ioo a b
  let R := U ∩ {x | 0 < gradNorm u x}
  have hS : IsOpen S := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo
  have hR : IsOpen R := isOpen_regularSet hU hu
  have hK : IsCompact (closure S) := hbdd.isCompact_closure
  have hfin : μ S ≠ ⊤ := (lt_of_le_of_lt (measure_mono subset_closure)
    (hμK _ hK hcl)).ne
  obtain ⟨φ, hφ, hcφ, hsφ, h01, hone⟩ := slab_critical_cutoff hU hu hab hbdd hcl hreg
  let W := interior (φ ⁻¹' {1})
  let V := R ∪ W
  let X : E3 → E3 := fun x =>
    (1 - φ x) • gradient (gradNorm u) x + gradNorm u x • gradient φ x
  have hW (x) (hx : x ∈ W) : φ =ᶠ[𝓝 x] (fun _ => 1) :=
    mem_interior_iff_mem_nhds.mp hx
  have hV : IsOpen V := hR.union isOpen_interior
  have hKV : closure S ⊆ V := by
    intro x hx
    by_cases hg : gradient u x = 0
    · exact Or.inr (mem_interior_iff_mem_nhds.mpr (hone x hx hg))
    · exact Or.inl ⟨hcl hx, norm_pos_iff.mpr hg⟩
  have hw (x) (hx : x ∈ R) : ContDiffAt ℝ 2 (gradNorm u) x :=
    gradNorm_contDiffAt_of_pos (hu.contDiffAt (hU.mem_nhds hx.1)) hx.2
  have hφ2 (x) : ContDiffAt ℝ 2 φ x := (hφ.of_le (by simp)).contDiffAt
  have hX : ContDiffOn ℝ 1 X V := by
    apply hV.contDiffOn_iff.mpr
    intro x hx
    rcases hx with hx | hx
    · exact slab_cutoff_field_contDiffAt (hw x hx) (hφ2 x)
    · exact contDiffAt_const.congr_of_eventuallyEq (slab_cutoff_field_near_one (hW x hx))
  have hdiv (x) (hx : x ∈ V) : vecDiv X x =
      (1 - φ x) * laplacianN (gradNorm u) x + gradNorm u x * laplacianN φ x := by
    rcases hx with hx | hx
    · exact slab_cutoff_field_div (hw x hx) (hφ2 x)
    · have he := slab_cutoff_field_near_one (w := gradNorm u) (hW x hx)
      have hfd := he.fderiv_eq (𝕜 := ℝ)
      have hd (i : Fin 3) : poissonCoordinateDerivative i (fun _ : E3 => (1 : ℝ)) =
          (fun _ => 0) := by
        funext y
        simp [poissonCoordinateDerivative]
      have hl : laplacianN φ x = 0 := (laplacianN_congr_nhds (hW x hx)).trans
        (by simp [laplacianN, hd, poissonCoordinateDerivative])
      simp [X, vecDiv, hfd, (hW x hx).self_of_nhds, hl]
  have hq : ContinuousOn (fun x => (1 - φ x) * laplacianN (gradNorm u) x) V := by
    intro x hx
    rcases hx with hx | hx
    · have hc := continuousOn_laplacianN_gradNorm_regular hR (hu.mono inter_subset_left)
        (fun _ hy => hy.2)
      exact ((continuousAt_const.sub hφ.continuous.continuousAt).mul
        (hc.continuousAt (hR.mem_nhds hx))).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hW x hx] with y hy
      simp [hy]
  have hp : ContinuousOn (fun x => gradNorm u x * laplacianN φ x) U :=
    (continuousOn_gradNorm hU hu).mul (continuous_laplacianN (hφ.of_le (by simp))).continuousOn
  have hiq : IntegrableOn (fun x => (1 - φ x) * laplacianN (gradNorm u) x) S :=
    ((hq.mono hKV).integrableOn_compact hK).mono_set subset_closure
  have hip : IntegrableOn (fun x => gradNorm u x * laplacianN φ x) S :=
    ((hp.mono hcl).integrableOn_compact hK).mono_set subset_closure
  have hiφ : IntegrableOn φ S μ := hφ.continuous.continuousOn.integrableOn_of_subset_isCompact
    hK hS.measurableSet subset_closure hfin
  have hi1φ : IntegrableOn (fun x => 1 - φ x) S μ :=
    (integrableOn_const hfin).sub hiφ
  have hqμ : (∫ x in S, (1 - φ x) * laplacianN (gradNorm u) x) =
      ∫ x in S, (1 - φ x) ∂μ := by
    symm
    apply slab_integral_regular_weight hU hu hΔ hμK hμ hS.measurableSet
    intro x hx hxr
    have hg : gradient u x = 0 := by
      by_contra hg
      exact hxr ⟨hx.1, norm_pos_iff.mpr hg⟩
    rw [(hone x (subset_closure hx) hg).self_of_nhds, sub_self]
  have hpμ : (∫ x in S, gradNorm u x * laplacianN φ x) = ∫ x in S, φ x ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_),
      hμ φ hφ hcφ (hsφ.trans inter_subset_left)]
    · symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)))
    · have hz : laplacianN φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (hsφ (tsupport_laplacianN_subset φ ht)))
      rw [hz, mul_zero]
  have hmass : (∫ x in S, vecDiv X x) = (μ S).toReal := by
    calc
      _ = ∫ x in S, ((1 - φ x) * laplacianN (gradNorm u) x +
          gradNorm u x * laplacianN φ x) :=
        setIntegral_congr_fun hS.measurableSet (fun x hx => hdiv x (hKV (subset_closure hx)))
      _ = (∫ x in S, (1 - φ x) ∂μ) + ∫ x in S, φ x ∂μ := by
        rw [integral_add hiq hip, hqμ, hpμ]
      _ = ∫ x in S, (1 : ℝ) ∂μ := by
        rw [← integral_add hi1φ hiφ]
        simp only [sub_add_cancel]
      _ = _ := by simp [measureReal_def]
  have hlevel (t : ℝ) (ht : t = a ∨ t = b) :
      (∫ x in U ∩ u ⁻¹' {t}, ⟪X x, gradient u x⟫ / gradNorm u x
        ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ x in U ∩ u ⁻¹' {t}, meanCurv u x * gradNorm u x
        ∂(Measure.euclideanHausdorffMeasure 2) := by
    have he : U ∩ u ⁻¹' {t} = R ∩ u ⁻¹' {t} := by
      ext x
      constructor
      · rintro ⟨hxU, hxt⟩
        refine ⟨⟨hxU, norm_pos_iff.mpr (hreg x hxU ?_)⟩, hxt⟩
        rcases ht with rfl | rfl
        · exact Or.inl hxt
        · exact Or.inr hxt
      · exact fun hx => ⟨hx.1.1, hx.2⟩
    apply setIntegral_congr_fun
      (he ▸ measurableSet_regular_inter_preimage hU hu (measurableSet_singleton t))
    intro x hx
    have hxt : u x = t := hx.2
    have hxs : x ∉ tsupport φ := by
      intro hs
      have hi := (hsφ hs).2
      rcases ht with rfl | rfl
      · exact (ne_of_gt hi.1) hxt
      · exact (ne_of_lt hi.2) hxt
    have hzero : φ =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hgradzero : gradient φ x = 0 := by simpa using hzero.gradient_eq
    have hpos : 0 < gradNorm u x := (he ▸ hx).1.2
    simp only [X, hzero.self_of_nhds, hgradzero, sub_zero, one_smul, smul_zero, add_zero]
    exact inner_gradient_gradNorm_div_eq
      ((hu.contDiffAt (hU.mem_nhds hx.1)).of_le (by norm_num)) hpos (hΔ x hx.1)
  calc
    _ = ∫ x in S, vecDiv X x := hmass.symm
    _ = _ := by rw [hGG hV hKV hX, hlevel b (Or.inr rfl), hlevel a (Or.inl rfl)]

/-- The norm times the identity has derivative zero at the origin. -/
private lemma slab_norm_smul_hasFDerivAt_zero :
    HasFDerivAt (fun v : E3 => ‖v‖ • v) (0 : E3 →L[ℝ] E3) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  have he (v : E3) :
      ‖v - 0‖⁻¹ * ‖‖v‖ • v - ‖(0 : E3)‖ • (0 : E3) - (0 : E3 →L[ℝ] E3) (v - 0)‖ =
        ‖v‖ := by
    by_cases hv : v = 0
    · simp [hv]
    · simp [norm_smul, norm_ne_zero_iff.mpr hv]
  simp_rw [he]
  simpa [ContinuousAt] using (continuousAt_id.norm : ContinuousAt (fun v : E3 => ‖v‖) 0)

/-- Although the norm itself is not differentiable at zero, its product with the
identity is continuously differentiable there. -/
private lemma slab_contDiff_norm_smul : ContDiff ℝ 1 (fun v : E3 => ‖v‖ • v) := by
  let D : E3 → E3 →L[ℝ] E3 := fun v =>
    ‖v‖ • ContinuousLinearMap.id ℝ E3 + (fderiv ℝ (fun y : E3 => ‖y‖) v).smulRight v
  have hd (v : E3) : HasFDerivAt (fun y : E3 => ‖y‖ • y) (D v) v := by
    by_cases hv : v = 0
    · subst v
      have hD0 : D 0 = 0 := by
        ext z i
        simp [D]
      rw [hD0]
      exact slab_norm_smul_hasFDerivAt_zero
    · exact ((contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) v).differentiableAt
        one_ne_zero).hasFDerivAt.smul (hasFDerivAt_id v)
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨D, ?_, hd⟩
  apply continuous_iff_continuousAt.mpr
  intro v
  apply ContinuousAt.add (continuousAt_id.norm.smul continuousAt_const)
  by_cases hv : v = 0
  · subst v
    change Tendsto (fun y : E3 => (fderiv ℝ (fun z : E3 => ‖z‖) y).smulRight y)
      (𝓝 0) (𝓝 ((fderiv ℝ (fun z : E3 => ‖z‖) 0).smulRight 0))
    simp only [ContinuousLinearMap.smulRight_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun y : E3 => ‖y‖) (𝓝 0) (𝓝 0) by
        simpa [ContinuousAt] using (continuousAt_id.norm : ContinuousAt (fun y : E3 => ‖y‖) 0))
      (fun _ => norm_nonneg _)
    intro y
    change ‖(fderiv ℝ (fun z : E3 => ‖z‖) y).smulRight y‖ ≤ ‖y‖
    rw [ContinuousLinearMap.norm_smulRight_apply]
    simpa using mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm : LipschitzWith 1 (fun z : E3 => ‖z‖)))
      (norm_nonneg y)
  · have hf : ContinuousAt (fderiv ℝ (fun y : E3 => ‖y‖)) v :=
      ((contDiffAt_norm ℝ hv : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖) v).fderiv_right
        (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).continuousAt
    exact ((ContinuousLinearMap.smulRightL ℝ E3 E3).continuous.continuousAt.comp hf).clm_apply
      continuousAt_id

/-- The Gauss-Green half of `lem:K-slab-F`. The vector field `|∇u| ∇u` is `C¹`,
including at the critical points, since `v ↦ |v| v` is `C¹` at zero. -/
theorem K_slab_F_gauss_green_of_gauss_green {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {a b : ℝ} (hab : a < b) (hbdd : Bornology.IsBounded (U ∩ u ⁻¹' Ioo a b))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0)
    (hGG : ∀ {V : Set E3}, IsOpen V → closure (U ∩ u ⁻¹' Ioo a b) ⊆ V →
      ∀ {X : E3 → E3}, ContDiffOn ℝ 1 X V →
      ∫ x in U ∩ u ⁻¹' Ioo a b, vecDiv X x =
        (∫ x in U ∩ u ⁻¹' {b}, ⟪X x, gradient u x⟫ / gradNorm u x
            ∂(Measure.euclideanHausdorffMeasure 2)) -
          ∫ x in U ∩ u ⁻¹' {a}, ⟪X x, gradient u x⟫ / gradNorm u x
            ∂(Measure.euclideanHausdorffMeasure 2)) :
    (∫ x in U ∩ u ⁻¹' {b}, gradNorm u x ^ 2 ∂(Measure.euclideanHausdorffMeasure 2)) -
        (∫ x in U ∩ u ⁻¹' {a}, gradNorm u x ^ 2 ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ x in U ∩ u ⁻¹' Ioo a b, ⟪gradient (gradNorm u) x, gradient u x⟫ := by
  let X : E3 → E3 := fun x => gradNorm u x • gradient u x
  have hgrad (x) (hx : x ∈ U) : ContDiffAt ℝ 1 (gradient u) x :=
    slab_contDiffAt_gradient ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))
  have hX : ContDiffOn ℝ 1 X U := slab_contDiff_norm_smul.comp_contDiffOn
    (fun x hx => (hgrad x hx).contDiffWithinAt)
  have hdiv (x) (hx : x ∈ U) : vecDiv X x = ⟪gradient (gradNorm u) x, gradient u x⟫ := by
    by_cases hg : gradient u x = 0
    · have hn : HasFDerivAt (fun v : E3 => ‖v‖ • v) (0 : E3 →L[ℝ] E3) (gradient u x) :=
        hg ▸ slab_norm_smul_hasFDerivAt_zero
      have hd := hn.comp x ((hgrad x hx).differentiableAt one_ne_zero).hasFDerivAt
      have he : fderiv ℝ X x = 0 := by
        simpa only [X, gradNorm, Function.comp_def, ContinuousLinearMap.zero_comp] using hd.fderiv
      simp only [vecDiv, he, zero_apply, PiLp.zero_apply, Finset.sum_const_zero,
        hg, inner_zero_right]
    · have hw : ContDiffAt ℝ 2 (gradNorm u) x :=
        gradNorm_contDiffAt_of_pos (hu.contDiffAt (hU.mem_nhds hx)) (norm_pos_iff.mpr hg)
      rw [slab_vecDiv_smul_gradient (hw.differentiableAt (by norm_num))
        ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)), hΔ x hx, mul_zero, add_zero]
  have hlevel (t : ℝ) (ht : t = a ∨ t = b) :
      (∫ x in U ∩ u ⁻¹' {t}, ⟪X x, gradient u x⟫ / gradNorm u x
        ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ^ 2
        ∂(Measure.euclideanHausdorffMeasure 2) := by
    have hpos (x) (hx : x ∈ U ∩ u ⁻¹' {t}) : 0 < gradNorm u x := by
      apply norm_pos_iff.mpr
      apply hreg x hx.1
      rcases ht with rfl | rfl
      · exact Or.inl hx.2
      · exact Or.inr hx.2
    have he : U ∩ u ⁻¹' {t} = (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} := by
      ext x
      exact ⟨fun hx => ⟨⟨hx.1, hpos x hx⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩
    apply setIntegral_congr_fun
      (he ▸ measurableSet_regular_inter_preimage hU hu (measurableSet_singleton t))
    intro x hx
    dsimp only [X]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    change gradNorm u x * gradNorm u x ^ 2 / gradNorm u x = gradNorm u x ^ 2
    exact mul_div_cancel_left₀ _ (hpos x hx).ne'
  calc
    _ = ∫ x in U ∩ u ⁻¹' Ioo a b, vecDiv X x := by
      rw [hGG hU hcl hX, hlevel b (Or.inr rfl), hlevel a (Or.inl rfl)]
    _ = _ := setIntegral_congr_fun
      (hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo).measurableSet
      (fun x hx => hdiv x hx.1)

end LiquidDrop.CapacitaryK
