module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# Complete integral curves on one-manifolds

Completeness is expressed by the given global integral curve `IsMIntegralCurve γ v`.
The model is the real line, with its boundaryless identity model with corners.
-/

namespace LiquidDrop

open Set Function Filter Manifold
open scoped Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) 1 M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, ℝ) x}
  {γ : ℝ → M} {t₀ : ℝ}

set_option backward.isDefEq.respectTransparency false in
/-- In the chart based at its value, a local integral curve has strict derivative
equal to the vector field at that value. -/
theorem oneManifold_integralCurveAt_hasStrictDerivAt
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hγ : IsMIntegralCurveAt γ v t₀) :
    HasStrictDerivAt (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ) (v (γ t₀)) t₀ := by
  have hc : ContinuousAt
      (fun x : M => tangentCoordChange 𝓘(ℝ, ℝ) x (γ t₀) x (v x)) (γ t₀) := by
    have hsec : ContinuousAt (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M))
        (γ t₀) := hv.continuous.continuousAt
    have hc := (continuousAt_extChartAt (I := 𝓘(ℝ, ℝ).tangent)
      (⟨γ t₀, v (γ t₀)⟩ : TangentBundle 𝓘(ℝ, ℝ) M)).comp
        (f := fun x : M => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)) hsec
    exact hc.snd
  have hd := hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    hγ.eventually_hasDerivAt (hc.comp hγ.continuousAt)
  rw [tangentCoordChange_self (I := 𝓘(ℝ, ℝ)) (mem_extChartAt_source (γ t₀))] at hd
  exact hd

variable
    (hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, ℝ) M)))
    (hv0 : ∀ x, v x ≠ 0)

include hv hv0

/-- A local integral curve of a nonvanishing field maps the neighbourhood filter
onto the neighbourhood filter at its value. -/
theorem oneManifold_integralCurveAt_map_nhds (hγ : IsMIntegralCurveAt γ v t₀) :
    map γ (𝓝 t₀) = 𝓝 (γ t₀) := by
  have hd := oneManifold_integralCurveAt_hasStrictDerivAt hv hγ
  have heq : (extChartAt 𝓘(ℝ, ℝ) (γ t₀)).symm ∘
      (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ) =ᶠ[𝓝 t₀] γ := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℝ)) (γ t₀))] with t ht
    exact (extChartAt 𝓘(ℝ, ℝ) (γ t₀)).left_inv ht
  calc
    map γ (𝓝 t₀) = map ((extChartAt 𝓘(ℝ, ℝ) (γ t₀)).symm ∘
        (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ)) (𝓝 t₀) := (map_congr heq).symm
    _ = map (extChartAt 𝓘(ℝ, ℝ) (γ t₀)).symm
        (map (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ) (𝓝 t₀)) := (map_map).symm
    _ = map (extChartAt 𝓘(ℝ, ℝ) (γ t₀)).symm
        (𝓝 (extChartAt 𝓘(ℝ, ℝ) (γ t₀) (γ t₀))) := by
      rw [hd.map_nhds_eq (hv0 (γ t₀))]
      rfl
    _ = 𝓝 (γ t₀) := by
      simpa only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] using
        map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, ℝ)) (γ t₀)

/-- Local integral curves of a nonvanishing field are injective on some neighbourhood. -/
theorem oneManifold_integralCurveAt_locally_injective (hγ : IsMIntegralCurveAt γ v t₀) :
    ∃ s ∈ 𝓝 t₀, InjOn γ s := by
  have hd := oneManifold_integralCurveAt_hasStrictDerivAt hv hγ
  obtain ⟨s, hs, hinv⟩ := (hd.eventually_left_inverse (hv0 (γ t₀))).exists_mem
  refine ⟨s, hs, ?_⟩
  intro a ha b hb hab
  have heq : (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ) a =
      (extChartAt 𝓘(ℝ, ℝ) (γ t₀) ∘ γ) b :=
    congrArg (extChartAt 𝓘(ℝ, ℝ) (γ t₀)) hab
  exact (hinv a ha).symm.trans ((congrArg _ heq).trans (hinv b hb))

/-- A complete integral curve of a nonvanishing field on a one-manifold is open. -/
theorem oneManifold_integralCurve_isOpenMap (hγ : IsMIntegralCurve γ v) : IsOpenMap γ :=
  isOpenMap_iff_nhds_le.mpr fun t =>
    (oneManifold_integralCurveAt_map_nhds hv hv0 (hγ.isMIntegralCurveAt t)).ge

variable [T2Space M]

/-- The complement of a complete orbit is open, by local existence and uniqueness. -/
theorem oneManifold_integralCurve_isOpen_compl_range (hγ : IsMIntegralCurve γ v) :
    IsOpen (range γ)ᶜ := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨δ, hδ0, hδ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := 𝓘(ℝ, ℝ))
      (v := v) (x₀ := x) (0 : ℝ) (hv x)
  obtain ⟨ε, hε, hδε⟩ := isMIntegralCurveAt_iff'.mp hδ
  have hball : Metric.ball (0 : ℝ) ε = Ioo (-ε) ε := by
    rw [Real.ball_eq_Ioo]; simp
  rw [hball] at hδε
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hn : δ '' Ioo (-ε) ε ∈ 𝓝 x := by
    rw [← hδ0, ← oneManifold_integralCurveAt_map_nhds hv hv0 hδ]
    exact image_mem_map (Ioo_mem_nhds h0.1 h0.2)
  apply mem_of_superset hn
  rintro y ⟨t, ht, rfl⟩ ⟨u, hu⟩
  have heq : EqOn δ (γ ∘ (· + (u - t))) (Ioo (-ε) ε) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht hv hδε
      ((hγ.comp_add (u - t)).isMIntegralCurveOn _) (by simpa using hu.symm)
  apply hx
  refine ⟨u - t, ?_⟩
  simpa only [comp_apply, zero_add, hδ0] using (heq h0).symm

/-- Completeness and connectedness make a nonvanishing one-dimensional orbit surjective. -/
theorem oneManifold_integralCurve_surjective [ConnectedSpace M]
    (hγ : IsMIntegralCurve γ v) : Surjective γ := by
  apply range_eq_univ.mp
  exact IsClopen.eq_univ
    ⟨isOpen_compl_iff.mp (oneManifold_integralCurve_isOpen_compl_range hv hv0 hγ),
      (oneManifold_integralCurve_isOpenMap hv hv0 hγ).isOpen_range⟩ (range_nonempty γ)

/-- An injective complete orbit parametrizes the manifold by a homeomorphism. -/
theorem oneManifold_integralCurve_homeomorph_real [ConnectedSpace M]
    (hγ : IsMIntegralCurve γ v) (hinj : Injective γ) :
    ∃ e : ℝ ≃ₜ M, ⇑e = γ := by
  exact ⟨Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective γ ⟨hinj, oneManifold_integralCurve_surjective hv hv0 hγ⟩) hγ.continuous
      (oneManifold_integralCurve_isOpenMap hv hv0 hγ), rfl⟩

/-- A periodic complete orbit of a nonvanishing field has a positive period on
whose half-open fundamental interval it is injective. -/
theorem oneManifold_integralCurve_exists_period_injOn
    (hγ : IsMIntegralCurve γ v) (hper : ∃ T > 0, Periodic γ T) :
    ∃ τ > 0, Periodic γ τ ∧ InjOn γ (Ico 0 τ) := by
  obtain ⟨s, hs, hinj⟩ :=
    oneManifold_integralCurveAt_locally_injective hv hv0 (hγ.isMIntegralCurveAt 0)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  have hreturn : ∀ t : ℝ, 0 < t → γ t = γ 0 → ε ≤ t := by
    intro t ht hγt
    by_contra h
    have hts : t ∈ s := hεs (by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using lt_of_not_ge h)
    exact (ne_of_gt ht) (hinj hts (mem_of_mem_nhds hs) hγt)
  obtain ⟨T, hT, hperiod⟩ := hper
  have hTret : γ T = γ 0 := by simpa only [zero_add] using hperiod 0
  have hclosed : IsClosed ({t : ℝ | γ t = γ 0} ∩ Ici ε) :=
    (isClosed_eq hγ.continuous continuous_const).inter isClosed_Ici
  have hleast := hclosed.isLeast_csInf
    ⟨T, hTret, hreturn T hT hTret⟩ ⟨ε, fun t ht => ht.2⟩
  set τ := sInf ({t : ℝ | γ t = γ 0} ∩ Ici ε)
  have hτ : 0 < τ := hε.trans_le hleast.1.2
  have hτret : γ τ = γ 0 := hleast.1.1
  have hτmin : ∀ t : ℝ, 0 < t → γ t = γ 0 → τ ≤ t :=
    fun t ht hγt => hleast.2 ⟨hγt, hreturn t ht hγt⟩
  refine ⟨τ, hτ, ?_, ?_⟩
  · simpa only [sub_zero] using hγ.periodic_of_eq hv hτret
  · intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hlt
    · have hp := hγ.periodic_of_eq hv hab.symm
      have hr : γ (b - a) = γ 0 := by simpa only [zero_add] using hp 0
      have := hτmin (b - a) (sub_pos.mpr hlt) hr
      linarith [ha.1, hb.2]
    · exact heq
    · have hp := hγ.periodic_of_eq hv hab
      have hr : γ (a - b) = γ 0 := by simpa only [zero_add] using hp 0
      have := hτmin (a - b) (sub_pos.mpr hlt) hr
      linarith [hb.1, ha.2]

/-- A fundamental period identifies a complete orbit with its additive circle. -/
theorem oneManifold_integralCurve_homeomorph_addCircle [ConnectedSpace M]
    (hγ : IsMIntegralCurve γ v) {τ : ℝ} (hτ : 0 < τ)
    (hper : Periodic γ τ) (hinj : InjOn γ (Ico 0 τ)) :
    ∃ e : AddCircle τ ≃ₜ M, ∀ t : ℝ, e (t : AddCircle τ) = γ t := by
  let : Fact (0 < τ) := ⟨hτ⟩
  have hrep (x : AddCircle τ) : ∃ t ∈ Ico (0 : ℝ) τ, (t : AddCircle τ) = x := by
    exact ⟨AddCircle.equivIco τ 0 x, by simpa only [zero_add] using
      (AddCircle.equivIco τ 0 x).property, AddCircle.coe_equivIco⟩
  have hlift_inj : Injective hper.lift := by
    intro x y hxy
    obtain ⟨a, ha, rfl⟩ := hrep x
    obtain ⟨b, hb, rfl⟩ := hrep y
    exact congrArg (fun t : ℝ => (t : AddCircle τ)) (hinj ha hb hxy)
  have hlift_surj : Surjective hper.lift := by
    intro x
    obtain ⟨t, rfl⟩ := oneManifold_integralCurve_surjective hv hv0 hγ x
    exact ⟨(t : AddCircle τ), hper.lift_coe t⟩
  have hlift_cont : Continuous hper.lift :=
    continuous_coinduced_dom.mpr hγ.continuous
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective hper.lift ⟨hlift_inj, hlift_surj⟩) hlift_cont,
    fun t => hper.lift_coe t⟩

/-- A complete integral curve of a nonvanishing `C¹` field on a connected Hausdorff
one-manifold is surjective and gives either a real-line or an additive-circle
parametrization. The global integral-curve hypothesis supplies completeness. -/
theorem oneManifold_classification_of_isMIntegralCurve [ConnectedSpace M]
    (hγ : IsMIntegralCurve γ v) :
    Surjective γ ∧
      ((Injective γ ∧ ∃ e : ℝ ≃ₜ M, ⇑e = γ) ∨
       (∃ τ > 0, Periodic γ τ ∧ InjOn γ (Ico 0 τ) ∧
         ∃ e : AddCircle τ ≃ₜ M, ∀ t : ℝ, e (t : AddCircle τ) = γ t)) := by
  refine ⟨oneManifold_integralCurve_surjective hv hv0 hγ, ?_⟩
  rcases (hγ.periodic_xor_injective hv).or with hper | hinj
  · obtain ⟨τ, hτ, hperiod, hinj⟩ :=
      oneManifold_integralCurve_exists_period_injOn hv hv0 hγ hper
    exact Or.inr ⟨τ, hτ, hperiod, hinj,
      oneManifold_integralCurve_homeomorph_addCircle hv hv0 hγ hτ hperiod hinj⟩
  · exact Or.inl ⟨hinj, oneManifold_integralCurve_homeomorph_real hv hv0 hγ hinj⟩

end LiquidDrop
