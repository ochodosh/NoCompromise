module

public import NoCompromise.Surface.RegularValue
public import NoCompromise.Surface.GaussExtension
public import NoCompromise.Surface.Morse

@[expose] public section

/-!
# Total curvature bound (blueprint chapter 14, `Surface/TotalCurvature`)

Facade for `lem:regular-fiber-finite` (in `Surface/RegularValue.lean`) and
`lem:gauss-map-extension` (in `Surface/GaussExtension.lean`); the index-sum items are proved here:

* `def:index-sum`: `localSign` and `indexSum`. For surfaces `S, S'` oriented by unit normal
  fields `n, n'` and an ambient representative `f`, the *oriented differential*
  `orientedDifferential n n' f p` acts as `d_pf` on `T_pS = (n p)ᗮ` and sends `n p` to
  `n' (f p)`. Its determinant is the determinant of `d_pf : T_pS → T_{f p}S'` in bases that are
  positively oriented by the normals (normal first), so `localSign = sign det d_pf` with the
  orientations. The index sum is the sum of local signs over the fibre at a regular value with
  finite fibre, and `0` otherwise (finiteness is automatic for compact `S`,
  `finite_fiber_of_isSurfaceRegularValue`).
* `conv:gauss-orientation`: for the Gauss map `n : S → S²`, with `S²` oriented by its outward
  normal `y ↦ y`, `det (orientedDifferential n id n p) = κ(p)`
  (`det_orientedDifferential_gaussMap`), hence `ε_n(p) = sign κ(p)`
  (`localSign_gaussMap`). This is proved, not assumed.
* `prop:index-sum-antipodal`: `gaussIndexSum_add_gaussIndexSum_neg`.
* `thm:total-curvature-bound` (PARTIAL): `total_curvature_le_of_total_curvature_index`, the
  antipodal averaging argument, with the three unproved inputs `thm:total-curvature-index`,
  `prop:morse-count` and the almost-everywhere regularity of the Gauss map (`cor:sard-charts`,
  not yet bridged to embedded surfaces) as named hypotheses.
-/

noncomputable section
open Set Function InnerProductSpace
namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- def:index-sum. The differential of `f` at `p` on `(n p)ᗮ`, completed by `n p ↦ n' (f p)`. -/
def orientedDifferential (n n' f : E₃ → E₃) (p : E₃) : E₃ →L[ℝ] E₃ :=
  fderiv ℝ f p ∘L (ContinuousLinearMap.id ℝ E₃ - (innerSL ℝ (n p)).smulRight (n p)) +
    (innerSL ℝ (n p)).smulRight (n' (f p))

/-- def:index-sum. `ε_f(p) = sign det d_pf`, computed with the orientations given by `n, n'`. -/
def localSign (n n' f : E₃ → E₃) (p : E₃) : ℤ :=
  (SignType.sign (LinearMap.det (orientedDifferential n n' f p : E₃ →ₗ[ℝ] E₃)) : ℤ)

open Classical in
/-- def:index-sum. `ι_y(f) = ∑_{p ∈ f⁻¹(y)} ε_f(p)` at a regular value (with finite fibre),
and `0` otherwise. -/
def indexSum (S S' : Set E₃) (n n' f : E₃ → E₃) (y : E₃) : ℤ :=
  if h : IsSurfaceRegularValue S S' f y ∧ {p ∈ S | f p = y}.Finite then
    ∑ p ∈ h.2.toFinset, localSign n n' f p
  else 0

/-- The index sum of the Gauss map `n : S → S²`, the sphere oriented by `y ↦ y`. -/
def gaussIndexSum (S : Set E₃) (n : E₃ → E₃) (y : E₃) : ℤ :=
  indexSum S (Metric.sphere (0 : E₃) 1) n (fun y => y) n y

/-- The number `c_λ` of critical points of `f|_S` of index `λ`. -/
def morseCount (S : Set E₃) (n : E₃ → E₃) (f : E₃ → ℝ) (k : ℕ) : ℕ :=
  Set.ncard {p | IsSurfaceCriticalPoint S f p ∧ surfaceIndex S n f p = k}

/-- conv:gauss-orientation. With `S` oriented by `n` and `S²` by its outward normal, the
oriented differential of the Gauss map has determinant the Gauss curvature. -/
theorem det_orientedDifferential_gaussMap {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    LinearMap.det (orientedDifferential n (fun y => y) n p : E₃ →ₗ[ℝ] E₃) =
      gaussCurvature S n p := by
  set T := tangentPlane S p
  set N : Submodule ℝ E₃ := ℝ ∙ n p
  have hTN : T = Nᗮ := hn.tangentPlane_eq hS hp
  have hc : IsCompl T N := by
    rw [hTN]
    exact N.isCompl_orthogonal.symm
  have hnp : ‖n p‖ = 1 := (hn.2 p hp).1
  let e : (T × N) ≃ₗ[ℝ] E₃ := Submodule.prodEquivOfIsCompl T N hc
  let A : T →ₗ[ℝ] T := (tangentShapeOperator S n p).toLinearMap
  have he (x : T × N) : e x = (x.1 : E₃) + (x.2 : E₃) := rfl
  have hkey : (orientedDifferential n (fun y => y) n p : E₃ →ₗ[ℝ] E₃) =
      (e : (T × N) →ₗ[ℝ] E₃) ∘ₗ (LinearMap.prodMap A LinearMap.id) ∘ₗ
        (e.symm : E₃ →ₗ[ℝ] (T × N)) := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := e.surjective v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, LinearMap.id_coe, id_eq]
    obtain ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩ := x
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx2
    have hx1' : inner ℝ (n p) x1 = 0 := by
      have : x1 ∈ Nᗮ := hTN ▸ hx1
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp this
    have hin : inner ℝ (n p) (x1 + t • n p) = t := by
      rw [inner_add_right, hx1', real_inner_smul_right, real_inner_self_eq_norm_sq, hnp]
      ring
    rw [he, he]
    change fderiv ℝ n p ((x1 + t • n p) - inner ℝ (n p) (x1 + t • n p) • n p) +
        inner ℝ (n p) (x1 + t • n p) • n p = (A ⟨x1, hx1⟩ : E₃) + t • n p
    rw [hin, add_sub_cancel_right]
    congr 1
    exact (hn.coe_tangentShapeOperator hS hp ⟨x1, hx1⟩).symm
  rw [hkey, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  rfl

/-- conv:gauss-orientation: `ε_n(p) = sign κ(p)`. -/
theorem localSign_gaussMap {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {p : E₃} (hp : p ∈ S) :
    localSign n (fun y => y) n p = (SignType.sign (gaussCurvature S n p) : ℤ) := by
  rw [localSign, det_orientedDifferential_gaussMap hS hn hp]

/-- A nonzero real whose `Real.sign` is `(-1)^k` has integer sign `(-1)^k`. -/
private lemma intSign_eq_of_realSign {x : ℝ} {k : ℕ} (hx : x ≠ 0)
    (h : Real.sign x = (-1 : ℝ) ^ k) : (SignType.sign x : ℤ) = (-1 : ℤ) ^ k := by
  have hcast : (((-1 : ℤ) ^ k : ℤ) : ℝ) = (-1 : ℝ) ^ k := by push_cast; rfl
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [sign_neg hneg]
    rw [Real.sign_of_neg hneg, ← hcast] at h
    exact_mod_cast h
  · rw [sign_pos hpos]
    rw [Real.sign_of_pos hpos, ← hcast] at h
    exact_mod_cast h

/-- Over a regular value `±v`, the Gauss-map index sum is the signed count of the critical
points of `h_v` in that fibre, the sign being `(-1)^{ind_p(h_v)}`. -/
private lemma gaussIndexSum_eq_sum {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {v y : E₃} (hv : ‖v‖ = 1) (hyv : y = v ∨ y = -v)
    (hy : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y) :
    gaussIndexSum S n y = ∑ p ∈ (finite_gaussMap_fiber hS hc hn hy).toFinset,
      (-1 : ℤ) ^ surfaceIndex S n (fun x => inner ℝ x v) p := by
  have hfin := finite_gaussMap_fiber hS hc hn hy
  unfold gaussIndexSum indexSum
  split_ifs with h0
  swap
  · exact absurd ⟨hy, hfin⟩ h0
  apply Finset.sum_congr rfl
  intro p hpF
  have hpF' : p ∈ S ∧ n p = y := hfin.mem_toFinset.mp hpF
  have hκ : gaussCurvature S n p ≠ 0 :=
    (isSurfaceRegularValue_normal_iff hS hn y).mp hy p hpF'.1 hpF'.2
  have hcrit : IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p :=
    (isSurfaceCriticalPoint_height_iff hS hn hpF'.1 hv).mpr (hpF'.2 ▸ hyv)
  rw [localSign_gaussMap hS hn hpF'.1]
  exact intSign_eq_of_realSign hκ
    (sign_gaussCurvature_eq_neg_one_pow_surfaceIndex hS hn hv hcrit hκ)

/-- prop:index-sum-antipodal: `ι_v(n) + ι_{-v}(n) = c₀ - c₁ + c₂` for the height `h_v`,
whenever `v` and `-v` are regular values of the Gauss map of a compact surface. -/
theorem gaussIndexSum_add_gaussIndexSum_neg {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {v : E₃} (hv : ‖v‖ = 1)
    (hreg : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v)
    (hreg' : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v)) :
    gaussIndexSum S n v + gaussIndexSum S n (-v) =
      (morseCount S n (fun x => inner ℝ x v) 0 : ℤ) -
        morseCount S n (fun x => inner ℝ x v) 1 + morseCount S n (fun x => inner ℝ x v) 2 := by
  classical
  set h : E₃ → ℝ := fun x => inner ℝ x v with hh
  set ind : E₃ → ℕ := fun p => surfaceIndex S n h p with hind
  have hF := finite_gaussMap_fiber hS hc hn hreg
  have hF' := finite_gaussMap_fiber hS hc hn hreg'
  have hC := finite_criticalPoints_height hS hc hn hv hreg hreg'
  have hsplit : hC.toFinset = hF.toFinset ∪ hF'.toFinset := by
    ext p
    simp only [Finite.mem_toFinset, Finset.mem_union]
    exact Set.ext_iff.mp (setOf_isSurfaceCriticalPoint_height hS hn hv) p
  have hdisj : Disjoint hF.toFinset hF'.toFinset := by
    rw [Finite.disjoint_toFinset]
    exact disjoint_normal_preimage_neg hv
  have hsum : gaussIndexSum S n v + gaussIndexSum S n (-v) =
      ∑ p ∈ hC.toFinset, (-1 : ℤ) ^ ind p := by
    rw [gaussIndexSum_eq_sum hS hc hn hv (Or.inl rfl) hreg,
      gaussIndexSum_eq_sum hS hc hn hv (Or.inr rfl) hreg', hsplit,
      Finset.sum_union hdisj]
  have hle : ∀ p ∈ hC.toFinset, ind p ≤ 2 := by
    intro p hp
    have hp' : IsSurfaceCriticalPoint S h p := hC.mem_toFinset.mp hp
    have := formIndex_le_finrank (tangentHessian S n h p)
    rw [hS.finrank_tangentPlane hp'.1] at this
    exact this
  have hpt : ∀ p ∈ hC.toFinset, (-1 : ℤ) ^ ind p =
      ((if ind p = 0 then 1 else 0) - (if ind p = 1 then 1 else 0)) +
        (if ind p = 2 then 1 else 0) := by
    intro p hp
    have := hle p hp
    interval_cases (ind p) <;> simp
  have hcount : ∀ k : ℕ, (morseCount S n h k : ℤ) =
      ∑ p ∈ hC.toFinset, (if ind p = k then (1 : ℤ) else 0) := by
    intro k
    rw [Finset.sum_boole, morseCount]
    have hset : {p | IsSurfaceCriticalPoint S h p ∧ surfaceIndex S n h p = k} =
        ↑(hC.toFinset.filter (fun p => ind p = k)) := by
      ext p
      simp only [Finset.coe_filter, Finite.mem_toFinset, mem_ofPred_eq, hind]
      exact Iff.rfl
    rw [hset, ncard_coe_finset]
  rw [hsum, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hcount 0, hcount 1, hcount 2]

open MeasureTheory in
/-- thm:total-curvature-bound, PARTIAL: `∫_Σ κ dH² ≤ 4π`, from the antipodal averaging argument.
The named hypotheses are the unproved inputs:
* `h_sard_charts` (cor:sard-charts, the input of the almost-everywhere clause of
  lem:morse-height, `ae_morse_height_of_sard_charts`): almost every point of `S²` is a regular
  value of the Gauss map;
* `h_morse_count` (prop:morse-count, for the compact connected surface `S`):
  `c₀ - c₁ + c₂ ≤ 2` for every Morse height function;
* `h_total_curvature_index` (thm:total-curvature-index): `y ↦ ι_y(n)` is integrable on `S²` and
  `∫_Σ κ dH² = ∫_{S²} ι_y(n) dH²(y)`. -/
theorem total_curvature_le_of_total_curvature_index {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y)
    (h_morse_count : ∀ v : E₃, ‖v‖ = 1 → IsSurfaceMorse S n (fun x => inner ℝ x v) →
      (morseCount S n (fun x => inner ℝ x v) 0 : ℤ) - morseCount S n (fun x => inner ℝ x v) 1 +
        morseCount S n (fun x => inner ℝ x v) 2 ≤ 2)
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi := by
  obtain ⟨hint, heq⟩ := h_total_curvature_index
  set μ := (hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1) with hμ
  set ι : E₃ → ℝ := fun y => (gaussIndexSum S n y : ℝ) with hι
  let e : E₃ ≃ᵢ E₃ := (LinearIsometryEquiv.neg ℝ : E₃ ≃ₗᵢ[ℝ] E₃).toIsometryEquiv
  have hsph : MeasurableSet (Metric.sphere (0 : E₃) 1) := Metric.isClosed_sphere.measurableSet
  have hmp : MeasurePreserving e μ μ := measurePreserving_neg_sphere
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hint' : Integrable (fun y => ι (-y)) μ := by
    have := (hmp.integrable_comp_emb hemb (g := ι)).mpr hint
    exact this
  have hflip : ∫ y, ι (-y) ∂μ = ∫ y, ι y ∂μ := hmp.integral_comp hemb ι
  have hreg' : ∀ᵐ y ∂μ, IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-y) :=
    hmp.quasiMeasurePreserving.ae h_sard_charts
  have hmem : ∀ᵐ y ∂μ, y ∈ Metric.sphere (0 : E₃) 1 := ae_restrict_mem hsph
  have hbound : ∀ᵐ y ∂μ, ι y + ι (-y) ≤ 2 := by
    filter_upwards [h_sard_charts, hreg', hmem] with y hy hy' hym
    have hv : ‖y‖ = 1 := by simpa using hym
    have hmorse := (isSurfaceMorse_height_iff hS hn hv).mpr ⟨hy, hy'⟩
    have hsum := gaussIndexSum_add_gaussIndexSum_neg hS hc hn hv hy hy'
    have hle := h_morse_count y hv hmorse
    have hZ : gaussIndexSum S n y + gaussIndexSum S n (-y) ≤ 2 := hsum ▸ hle
    change (gaussIndexSum S n y : ℝ) + (gaussIndexSum S n (-y) : ℝ) ≤ 2
    exact_mod_cast hZ
  have hμuniv : μ Set.univ = ENNReal.ofReal (4 * Real.pi) := by
    rw [hμ, Measure.restrict_apply_univ]
    exact hausdorffMeasure2_unit_sphere
  have : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.ofReal_lt_top⟩
  have hconst : ∫ _y, (2 : ℝ) ∂μ = 2 * (4 * Real.pi) := by
    rw [integral_const, smul_eq_mul, Measure.real, hμuniv,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hmono : ∫ y, (ι y + ι (-y)) ∂μ ≤ ∫ _y, (2 : ℝ) ∂μ :=
    integral_mono_ae (hint.add hint') (integrable_const 2) hbound
  rw [integral_add hint hint', hflip, hconst] at hmono
  rw [heq]
  change ∫ y, ι y ∂μ ≤ 4 * Real.pi
  linarith

end LiquidDrop
