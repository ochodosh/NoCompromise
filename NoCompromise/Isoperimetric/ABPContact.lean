import NoCompromise.Ball.Perimeter
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal InnerProductSpace

namespace LiquidDrop

/-- The Hessian quadratic form `D²z(x)(v,v)`. -/
def hessianForm (z : AmbientSpace → ℝ) (x v : AmbientSpace) : ℝ :=
  fderiv ℝ (fderiv ℝ z) x v v

/-- The Laplacian as the trace of the Hessian in the standard basis. -/
def laplacianTrace (z : AmbientSpace → ℝ) (x : AmbientSpace) : ℝ :=
  ∑ i : Fin 3, hessianForm z x (EuclideanSpace.single i 1)

/-- The lower contact set `Γ`. -/
def abpContactSet (G : Set AmbientSpace) (z : AmbientSpace → ℝ) : Set AmbientSpace :=
  {x | x ∈ G ∧ ∀ y ∈ closure G, z x + ⟪gradient z x, y - x⟫_ℝ ≤ z y}

/-- The Neumann condition, expressed using an inward ray and its one-sided derivative. -/
def NeumannOne (G : Set AmbientSpace) (z : AmbientSpace → ℝ) : Prop :=
  ∀ x ∈ frontier G, ∃ ν : AmbientSpace, ‖ν‖ = 1 ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), x - t • ν ∈ G) ∧
    HasDerivWithinAt (fun t : ℝ => z (x - t • ν)) (-1) (Ici 0) 0

/-- A local minimum has nonnegative second derivative whenever it is defined. -/
private lemma second_deriv_nonneg {f : ℝ → ℝ} {a : ℝ}
    (hm : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra! hn
  have hM := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hM] with t ht ht'
    exact le_antisymm ht' ht
  have he' : deriv f =ᶠ[𝓝 a] (fun _ : ℝ => 0) := by
    simpa only [deriv_const'] using he.deriv
  have he'' : deriv (deriv f) a = 0 := by
    simpa only [deriv_const] using he'.deriv_eq
  linarith

/-- Blueprint `lem:abp-contact`, second half: `D²z ≥ 0` on `Γ`. -/
theorem hessianForm_nonneg_of_mem_abpContactSet {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace}
    (hx : x ∈ abpContactSet G z) (v : AmbientSpace) : 0 ≤ hessianForm z x v := by
  let p := gradient z x
  let f : ℝ → ℝ := fun t => z (x + t • v) - ⟪p, x + t • v⟫_ℝ
  have hzAt : ContDiffAt ℝ 2 z x := hz.contDiffAt (hGo.mem_nhds hx.1)
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ G := by
    have hc : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa only [ContinuousAt, zero_smul, add_zero] using (hline 0).continuousAt
    exact hc.eventually (hGo.mem_nhds hx.1)
  have hm : IsLocalMin f 0 := by
    filter_upwards [he] with t ht
    have h := hx.2 (x + t • v) (subset_closure ht)
    dsimp [f, p]
    simp only [zero_smul, add_zero, inner_sub_right] at *
    linarith
  have hd (t : ℝ) (ht : x + t • v ∈ G) :
      HasDerivAt f (fderiv ℝ z (x + t • v) v - ⟪p, v⟫_ℝ) t := by
    have hd := (hz.contDiffAt (hGo.mem_nhds ht)).differentiableAt (by norm_num)
    convert! (hd.hasFDerivAt.comp_hasDerivAt t (hline t)).sub
      ((hasDerivAt_const t p).inner ℝ (hline t)) using 1
    simp
  have hd0 := hd 0 (by simpa using hx.1)
  have hde : deriv f =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ z (x + t • v) v - ⟪p, v⟫_ℝ) := by
    filter_upwards [he] with t ht using (hd t ht).deriv
  have hdz : DifferentiableAt ℝ (fderiv ℝ z) x :=
    (hzAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdd : HasDerivAt (fun t : ℝ => fderiv ℝ z (x + t • v))
      (fderiv ℝ (fderiv ℝ z) x v) 0 := by
    convert! hdz.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) (by simp) using 1
  have hdd' := (hdd.clm_apply (hasDerivAt_const 0 v)).sub_const ⟪p, v⟫_ℝ
  have hh : deriv (deriv f) 0 = hessianForm z x v := by
    rw [hde.deriv_eq, hdd'.deriv]
    simp [hessianForm]
  rw [← hh]
  exact second_deriv_nonneg hm hd0.continuousAt

/-- Blueprint `lem:abp-contact`, first half: `B_1 ⊆ ∇z(Γ)`. -/
theorem ball_subset_gradient_image_abpContactSet {G : Set AmbientSpace}
    (hGb : Bornology.IsBounded G) (hGo : IsOpen G) (hGne : G.Nonempty)
    {z : AmbientSpace → ℝ}
    (hz : ContDiffOn ℝ 2 z G) (hzc : ContinuousOn z (closure G)) (hN : NeumannOne G z) :
    ball (0 : AmbientSpace) 1 ⊆ gradient z '' abpContactSet G z := by
  intro p hp
  have hp1 : ‖p‖ < 1 := by simpa [mem_ball, dist_zero_right] using hp
  let w : AmbientSpace → ℝ := fun y => z y - ⟪p, y⟫_ℝ
  have hwc : ContinuousOn w (closure G) :=
    hzc.sub (continuous_const.inner continuous_id).continuousOn
  obtain ⟨x, hxc, hm⟩ := hGb.isCompact_closure.exists_isMinOn
    (hGne.mono subset_closure) hwc
  have hx : x ∈ G := by
    by_contra hx
    have hxf : x ∈ frontier G := by
      rw [frontier, hGo.interior_eq]
      exact ⟨hxc, hx⟩
    obtain ⟨ν, hν, hray, hder⟩ := hN x hxf
    have hip : ⟪p, ν⟫_ℝ < 1 := by
      calc
        _ ≤ ‖p‖ * ‖ν‖ := real_inner_le_norm p ν
        _ < 1 := by simpa [hν] using hp1
    have hline : HasDerivAt (fun t : ℝ => x - t • ν) (-ν) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub x
    have hinner := (hasDerivAt_const (0 : ℝ) p).inner ℝ hline
    have hwd : HasDerivWithinAt (fun t : ℝ => w (x - t • ν))
        (-1 + ⟪p, ν⟫_ℝ) (Ici 0) 0 := by
      convert! hder.sub hinner.hasDerivWithinAt using 1
      simp
    have hbelow := hwd.Ioi_of_Ici.limsup_slope_le' (by simp) (by linarith :
      -1 + ⟪p, ν⟫_ℝ < 0)
    have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, htG, hts⟩ := (htpos.and (hray.and hbelow)).exists
    have hmin : w x ≤ w (x - t • ν) := hm (subset_closure htG)
    have hneg : w (x - t • ν) - w x < 0 := by
      have hts' : (w (x - t • ν) - w x) / t < 0 := by
        simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using hts
      rcases div_neg_iff.mp hts' with h | h
      · exact False.elim ((not_lt_of_ge ht.le) h.2)
      · exact h.1
    linarith
  have hloc : IsLocalMin w x := hm.isLocalMin
    (mem_of_superset (hGo.mem_nhds hx) subset_closure)
  have hdz := (hz.contDiffAt (hGo.mem_nhds hx)).differentiableAt (by norm_num)
  have hlin : HasFDerivAt (fun y : AmbientSpace => ⟪p, y⟫_ℝ) (innerSL ℝ p) x :=
    (innerSL ℝ p).hasFDerivAt
  have hzero : fderiv ℝ z x - innerSL ℝ p = 0 := by
    rw [← (hdz.hasFDerivAt.sub hlin).fderiv]
    exact hloc.fderiv_eq_zero
  have hgrad : gradient z x = p := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left]
    exact congrArg (fun L : AmbientSpace →L[ℝ] ℝ => L v) (sub_eq_zero.mp hzero)
  refine ⟨x, ⟨hx, ?_⟩, hgrad⟩
  intro y hy
  have hmin : w x ≤ w y := hm hy
  dsimp [w] at hmin
  rw [hgrad, inner_sub_right]
  linarith

/-- The gradient derivative, obtained from the Hessian by the Riesz identification. -/
private def abpGradientDeriv (z : AmbientSpace → ℝ) (x : AmbientSpace) :
    AmbientSpace →L[ℝ] AmbientSpace :=
  (InnerProductSpace.toDual ℝ AmbientSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L fderiv ℝ (fderiv ℝ z) x

private lemma inner_abpGradientDeriv (z : AmbientSpace → ℝ) (x v w : AmbientSpace) :
    ⟪abpGradientDeriv z x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ z) x v w := by
  exact InnerProductSpace.toDual_symm_apply

private lemma hasFDerivAt_gradient {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace} (hx : x ∈ G) :
    HasFDerivAt (gradient z) (abpGradientDeriv z x) x := by
  have hd := ((hz.contDiffAt (hGo.mem_nhds hx)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let R := (InnerProductSpace.toDual ℝ AmbientSpace).symm.toContinuousLinearEquiv
  exact R.toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt

/-- The lower contact set of a twice continuously differentiable function is measurable. -/
theorem measurableSet_abpContactSet {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) :
    MeasurableSet (abpContactSet G z) := by
  have hg : ContinuousOn (gradient z) G := by
    intro x hx
    exact (hasFDerivAt_gradient hGo hz hx).continuousAt.continuousWithinAt
  have ho : IsOpen (G \ abpContactSet G z) := by
    have he : G \ abpContactSet G z =
        ⋃ y ∈ closure G, G ∩ {x | z y < z x + ⟪gradient z x, y - x⟫_ℝ} := by
      ext x
      simp only [Set.mem_sdiff, abpContactSet, mem_ofPred_eq, not_and, not_forall, not_le,
        mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨hx, h⟩
        obtain ⟨y, hy, hh⟩ := h hx
        exact ⟨y, hy, hx, hh⟩
      · rintro ⟨y, hy, hx, hh⟩
        exact ⟨hx, fun _ => ⟨y, hy, hh⟩⟩
    rw [he]
    refine isOpen_iUnion fun y => isOpen_iUnion fun _ => ?_
    exact (hz.continuousOn.add (hg.inner
      (continuousOn_const.sub continuousOn_id))).isOpen_inter_preimage hGo isOpen_Ioi
  have he : abpContactSet G z = G \ (G \ abpContactSet G z) := by
    ext x
    simp only [Set.mem_sdiff]
    exact ⟨fun hx => ⟨hx.1, fun h => h.2 hx⟩, fun hx => by tauto⟩
  rw [he]
  exact hGo.measurableSet.diff ho.measurableSet

private lemma abp_amgm_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h (a b c : ℝ) (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
      27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
    have h1 := mul_nonneg hc (sq_nonneg (a - b))
    have h2 := mul_nonneg hc (mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb))
    have h3 := pow_nonneg (by linarith : 0 ≤ a + b - 2 * c) 3
    nlinarith only [h1, h2, h3]
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · have := h b c a ha hab hac
      nlinarith only [this]
    · have := h a b c hc hca (hca.trans hab)
      nlinarith only [this]
  · rcases le_total b c with hbc | hcb
    · have := h a c b hb hba hbc
      nlinarith only [this]
    · have := h a b c hc (hcb.trans hba) hcb
      nlinarith only [this]

private lemma abs_det_abpGradientDeriv_le {G : Set AmbientSpace} (hGo : IsOpen G)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) {x : AmbientSpace}
    (hx : x ∈ abpContactSet G z) :
    |(abpGradientDeriv z x).det| ≤ (laplacianTrace z x / 3) ^ 3 := by
  let T := (abpGradientDeriv z x).toLinearMap
  have hs : T.IsSymmetric := by
    intro v w
    change ⟪abpGradientDeriv z x v, w⟫_ℝ = ⟪v, abpGradientDeriv z x w⟫_ℝ
    rw [real_inner_comm (abpGradientDeriv z x w) v, inner_abpGradientDeriv, inner_abpGradientDeriv]
    exact (hz.contDiffAt (hGo.mem_nhds hx.1)).isSymmSndFDerivAt (by simp) v w
  have hp : T.IsPositive := by
    refine ⟨hs, fun v => ?_⟩
    change 0 ≤ ⟪abpGradientDeriv z x v, v⟫_ℝ
    rw [inner_abpGradientDeriv]
    exact hessianForm_nonneg_of_mem_abpContactSet hGo hz hx v
  have hn : Module.finrank ℝ AmbientSpace = 3 := finrank_euclideanSpace_fin
  have ht : T.trace ℝ AmbientSpace = laplacianTrace z x := by
    rw [LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (Fin 3) ℝ)]
    unfold laplacianTrace
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply, real_inner_comm]
    exact inner_abpGradientDeriv z x _ _
  have he : ∑ i, hs.eigenvalues hn i = laplacianTrace z x := by
    simpa using (hs.trace_eq_sum_eigenvalues hn).symm.trans ht
  have hd : (abpGradientDeriv z x).det = ∏ i, hs.eigenvalues hn i :=
    hs.det_eq_prod_eigenvalues hn
  rw [hd, abs_of_nonneg (Finset.prod_nonneg fun i _ => hp.nonneg_eigenvalues hn i)]
  rw [← he, Fin.prod_univ_three, Fin.sum_univ_three]
  exact abp_amgm_three (hp.nonneg_eigenvalues hn 0) (hp.nonneg_eigenvalues hn 1)
    (hp.nonneg_eigenvalues hn 2)

/-- The ABP volume bound (core of blueprint `prop:iso-smooth`). -/
theorem abp_volume_bound {G : Set AmbientSpace}
    (hGb : Bornology.IsBounded G) (hGo : IsOpen G) (hGne : G.Nonempty)
    {z : AmbientSpace → ℝ}
    (hz : ContDiffOn ℝ 2 z G) (hzc : ContinuousOn z (closure G)) (hN : NeumannOne G z)
    {c : ℝ} (hlap : ∀ x ∈ G, laplacianTrace z x = c) :
    ENNReal.ofReal (4 * Real.pi / 3) ≤ volume G * ENNReal.ofReal ((c / 3) ^ 3) := by
  have hm := measurableSet_abpContactSet hGo hz
  calc
    ENNReal.ofReal (4 * Real.pi / 3) = volume (ball (0 : AmbientSpace) 1) := by
      rw [volume_ball_eq_ofReal _ zero_le_one]
      norm_num
    _ ≤ volume (gradient z '' abpContactSet G z) := measure_mono
      (ball_subset_gradient_image_abpContactSet hGb hGo hGne hz hzc hN)
    _ ≤ ∫⁻ x in abpContactSet G z, ENNReal.ofReal |(abpGradientDeriv z x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hm
        (fun _ hx => (hasFDerivAt_gradient hGo hz hx.1).hasFDerivWithinAt)
    _ ≤ ∫⁻ _ in abpContactSet G z, ENNReal.ofReal ((c / 3) ^ 3) := by
      apply setLIntegral_mono' hm
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      simpa only [hlap x hx.1] using abs_det_abpGradientDeriv_le hGo hz hx
    _ = ENNReal.ofReal ((c / 3) ^ 3) * volume (abpContactSet G z) :=
      setLIntegral_const _ _
    _ ≤ volume G * ENNReal.ofReal ((c / 3) ^ 3) := by
      rw [mul_comm]
      exact mul_le_mul_left (measure_mono fun _ hx => hx.1) _

/-- Blueprint `prop:iso-smooth`, given the Neumann solution of `lem:abp-neumann`
(`Δz = P(G)/|G|`, `∂_ν z = 1`). -/
theorem iso_smooth_of_neumann_solution {G : Set AmbientSpace}
    (hGb : Bornology.IsBounded G) (hGo : IsOpen G) (hGne : G.Nonempty)
    {z : AmbientSpace → ℝ} (hz : ContDiffOn ℝ 2 z G) (hzc : ContinuousOn z (closure G))
    (hN : NeumannOne G z)
    (hlap : ∀ x ∈ G, laplacianTrace z x = (perimeter G).toReal / volume.real G) :
    36 * Real.pi * volume.real G ^ 2 ≤ (perimeter G).toReal ^ 3 := by
  have hV : 0 < volume.real G :=
    ENNReal.toReal_pos_iff.mpr ⟨hGo.measure_pos volume hGne, hGb.measure_lt_top⟩
  have hP : 0 ≤ (perimeter G).toReal := ENNReal.toReal_nonneg
  have hb := abp_volume_bound hGb hGo hGne hz hzc hN hlap
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hGb.measure_lt_top.ne ENNReal.ofReal_ne_top) hb
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hr
  change 4 * Real.pi / 3 ≤ volume.real G *
    ((perimeter G).toReal / volume.real G / 3) ^ 3 at hr
  have he : volume.real G * ((perimeter G).toReal / volume.real G / 3) ^ 3 =
      (perimeter G).toReal ^ 3 / (27 * volume.real G ^ 2) := by
    field_simp
    ring
  rw [he] at hr
  have hh := (le_div_iff₀ (by positivity : 0 < 27 * volume.real G ^ 2)).mp hr
  nlinarith only [hh]

end LiquidDrop
