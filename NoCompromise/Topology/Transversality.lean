import NoCompromise.Surface.Geometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Order.IntermediateValue

/-!
# Topological one-manifolds with boundary; relative transversality

* `lem:handshake` (PARTIAL): topological one-manifolds with boundary are modelled on
  the closed half-line `ℝ≥0` by open partial homeomorphisms. A boundary point is one
  sent to `0` by some chart; every chart then sends it to `0`
  (`oneManifoldBoundary_chart_eq_zero`), and the boundary of a compact one-manifold is
  finite (`oneManifoldBoundary_finite`). Evenness of its cardinality is still open.
* `thm:transversality` (PARTIAL): the definition `TransverseAt`, the relative cutoff,
  the uniform `C¹` smallness of cutoff perturbations, and the assembly lemma
  `exists_relative_perturbation_of_good_parameters`, which derives the theorem's
  conclusion from the generic-parameter (Sard) assertion `hgood`. Smoothness on the
  closed ball is expressed by a globally smooth ambient representative.
-/

noncomputable section
open Set Filter Function
open scoped Topology NNReal

namespace LiquidDrop

-- BEGIN lem:handshake
section Handshake

variable {X : Type*} [TopologicalSpace X]

/-- A subset is a topological one-manifold with boundary if its subtype is covered by
open partial homeomorphisms to the closed half-line `ℝ≥0 = {t : ℝ // 0 ≤ t}`.
Both chart sources and chart targets are open in their respective subtype topologies. -/
def IsOneManifoldWithBoundary (C : Set X) : Prop :=
  ∀ x : C, ∃ e : OpenPartialHomeomorph C ℝ≥0, x ∈ e.source

/-- The manifold boundary consists of points sent to zero by some half-line chart.
This is an existential chart definition, independent of any chosen atlas. -/
def oneManifoldBoundary (C : Set X) : Set X :=
  {x | ∃ hx : x ∈ C, ∃ e : OpenPartialHomeomorph C ℝ≥0,
    (⟨x, hx⟩ : C) ∈ e.source ∧ e ⟨x, hx⟩ = 0}

private theorem halfLineChart_eq_zero
    (e : OpenPartialHomeomorph ℝ≥0 ℝ≥0) {x : ℝ≥0}
    (hx : x ∈ e.source) (hzero : e x = 0) : x = 0 := by
  by_contra h
  have hxpos : 0 < x := lt_of_le_of_ne (zero_le : 0 ≤ x) (Ne.symm h)
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0, hxpos⟩ (exists_gt x)).mp
      (e.open_source.mem_nhds hx)
  obtain ⟨c, hac, hcx⟩ := exists_between hax
  obtain ⟨d, hxd, hdb⟩ := exists_between hxb
  have hsub : Icc c d ⊆ e.source := by
    intro y hy
    exact hab ⟨hac.trans_le hy.1, hy.2.trans_lt hdb⟩
  have hc : c ∈ Icc c d := ⟨le_rfl, (hcx.trans hxd).le⟩
  have hd : d ∈ Icc c d := ⟨(hcx.trans hxd).le, le_rfl⟩
  have hx' : x ∈ Icc c d := ⟨hcx.le, hxd.le⟩
  rcases (e.continuousOn.mono hsub).strictMonoOn_of_injOn_Icc'
      (hcx.trans hxd).le (e.injOn.mono hsub) with hm | hm
  · have := hm hc hx' hcx
    rw [hzero] at this
    exact (not_lt_of_ge (zero_le : 0 ≤ e c)) this
  · have := hm hx' hd hxd
    rw [hzero] at this
    exact (not_lt_of_ge (zero_le : 0 ≤ e d)) this

/-- Every half-line chart containing a boundary point sends it to zero. -/
theorem oneManifoldBoundary_chart_eq_zero {C : Set X}
    {x : C} (hx : (x : X) ∈ oneManifoldBoundary C)
    (e : OpenPartialHomeomorph C ℝ≥0) (he : x ∈ e.source) : e x = 0 := by
  obtain ⟨hxC, f, hf, hfzero⟩ := hx
  have hf' : x ∈ f.source := hf
  have hfzero' : f x = 0 := hfzero
  apply halfLineChart_eq_zero (e.symm.trans f)
  · refine ⟨e.map_source he, ?_⟩
    change e.symm (e x) ∈ f.source
    simpa only [e.left_inv he] using hf'
  · simpa only [OpenPartialHomeomorph.trans_apply, e.left_inv he] using hfzero'

/-- A single half-line chart contains at most one boundary point. -/
theorem oneManifoldBoundary_chart_subsingleton {C : Set X}
    (e : OpenPartialHomeomorph C ℝ≥0) :
    (e.source ∩ ((↑) : C → X) ⁻¹' oneManifoldBoundary C).Subsingleton := by
  intro x hx y hy
  apply e.injOn hx.1 hy.1
  exact (oneManifoldBoundary_chart_eq_zero hx.2 e hx.1).trans
    (oneManifoldBoundary_chart_eq_zero hy.2 e hy.1).symm

/-- Compactness and a finite chart cover imply that the manifold boundary is finite.
This part does not require a separation assumption on the ambient space. -/
theorem oneManifoldBoundary_finite {C : Set X}
    (hC : IsCompact C) (hM : IsOneManifoldWithBoundary C) :
    (oneManifoldBoundary C).Finite := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  choose e he using hM
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : C => (e x).source)
    (fun x => (e x).open_source) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, he x⟩)
  have hfinite : (((↑) : C → X) ⁻¹' oneManifoldBoundary C).Finite := by
    apply (t.finite_toSet.biUnion (fun x _ =>
      (oneManifoldBoundary_chart_subsingleton (e x)).finite)).subset
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact mem_iUnion₂.mpr ⟨y, hy, hxy, hx⟩
  apply (hfinite.image ((↑) : C → X)).subset
  intro x hx
  have hxC : x ∈ C := hx.choose
  exact ⟨⟨x, hxC⟩, hx, rfl⟩

end Handshake
-- END lem:handshake

-- BEGIN thm:transversality

set_option maxSynthPendingDepth 8

/-- `f` is transverse to `S` at `p`. -/
def TransverseAt (S : Set E₃) {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → E₃)
    (p : EuclideanSpace ℝ (Fin k)) : Prop :=
  f p ∈ S →
    LinearMap.range (fderiv ℝ f p : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E₃) ⊔
      tangentPlane S (f p) = ⊤

/-- A relative cutoff for the closed unit ball. It equals one off the prescribed
boundary neighbourhood and vanishes on an ambient open neighbourhood of the sphere. -/
theorem exists_relative_transversality_cutoff {k : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin k))} (hW : IsOpen W)
    (hWb : Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ W) :
    ∃ χ : EuclideanSpace ℝ (Fin k) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, p ∉ W → χ p = 1) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧
        Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ V ∧ ∀ p ∈ V, χ p = 0) := by
  let K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 \ W
  have hK : IsCompact K := (isCompact_closedBall _ _).diff hW
  have hKi : K ⊆ Metric.ball 0 1 := by
    intro p hp
    have hpball : dist p 0 ≤ 1 := hp.1
    have hpne : dist p 0 ≠ 1 := fun he => hp.2 (hWb he)
    exact lt_of_le_of_ne hpball hpne
  obtain ⟨χ, hχ, hcχ, hsχ, hχone, hχb⟩ :=
    exists_smooth_cutoff_one_near_compact hK Metric.isOpen_ball hKi
  refine ⟨χ, hχ, hcχ, hχb, ?_, (tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl, ?_, ?_⟩
  · intro p hp hpW
    exact (hχone.filter_mono (nhds_le_nhdsSet (show p ∈ K from ⟨hp, hpW⟩))).self_of_nhds
  · intro p hp hps
    have hplt : dist p 0 < 1 := hsχ hps
    have hpeq : dist p 0 = 1 := hp
    exact (ne_of_lt hplt) hpeq
  · intro p hp
    by_contra hn
    exact hp (subset_tsupport χ hn)

/-- The derivative of a cutoff perturbation, as an operator on ambient vectors. -/
theorem fderiv_cutoff_perturbation {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {χ : EuclideanSpace ℝ (Fin k) → ℝ}
    {p : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f p)
    (hχ : DifferentiableAt ℝ χ p) (v : E₃) :
    fderiv ℝ (fun q => f q + χ q • v) p =
      fderiv ℝ f p + (fderiv ℝ χ p).smulRight v :=
  (hf.hasFDerivAt.add (hχ.hasFDerivAt.smul_const v)).fderiv

/-- At a zero of a nonnegative cutoff the perturbation changes neither the value
nor the derivative. This includes zeros on the edge of the cutoff's support. -/
theorem transverseAt_cutoff_perturbation_of_zero {k : ℕ} {S : Set E₃}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {χ : EuclideanSpace ℝ (Fin k) → ℝ}
    {p : EuclideanSpace ℝ (Fin k)} (hf : DifferentiableAt ℝ f p)
    (hχ : DifferentiableAt ℝ χ p) (hχnonneg : ∀ q, 0 ≤ χ q) (hχp : χ p = 0)
    (v : E₃) :
    TransverseAt S (fun q => f q + χ q • v) p ↔ TransverseAt S f p := by
  have hmin : IsLocalMin χ p := Filter.Eventually.of_forall fun q => by
    rw [hχp]
    exact hχnonneg q
  have hd : fderiv ℝ (fun q => f q + χ q • v) p = fderiv ℝ f p := by
    rw [fderiv_cutoff_perturbation hf hχ v, hmin.fderiv_eq_zero]
    ext u
    simp
  simp only [TransverseAt, hd, hχp, zero_smul, add_zero]

/-- Small parameters give uniform C¹-small perturbations on the closed unit ball.
The ambient representatives are globally smooth, as in the relative theorem. -/
theorem exists_cutoff_perturbation_radius {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {χ : EuclideanSpace ℝ (Fin k) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : E₃, ‖v‖ < δ →
      ContDiff ℝ (⊤ : ℕ∞) (fun p => f p + χ p • v) ∧
      ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        ‖(f p + χ p • v) - f p‖ < ε ∧
          ‖fderiv ℝ (fun q => f q + χ q • v) p - fderiv ℝ f p‖ < ε := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).exists_bound_of_continuousOn
      (hχ.continuous_fderiv (by simp)).continuousOn
  have hCpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨ε / max C 1, div_pos hε hCpos,
    fun v hv => ⟨hf.add (hχ.smul contDiff_const), fun p hp => ?_⟩⟩
  have hprod : max C 1 * ‖v‖ < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hCpos).mp hv
  have hvε : ‖v‖ < ε := calc
    ‖v‖ = 1 * ‖v‖ := (one_mul _).symm
    _ ≤ max C 1 * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    _ < ε := hprod
  constructor
  · simpa only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hχb p).1] using
      (mul_le_of_le_one_left (norm_nonneg v) (hχb p).2).trans_lt hvε
  · rw [fderiv_cutoff_perturbation (hf.differentiable (by simp) p)
      (hχ.differentiable (by simp) p), add_sub_cancel_left,
      ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul_of_nonneg_right ((hC p hp).trans (le_max_left _ _))
      (norm_nonneg v)).trans_lt hprod

/-- Linear algebra underlying the local projection criterion. In an incidence
chart, `A` is the derivative of the perturbed map and `B` is the surface-chart
derivative; the projection derivative is `a⁻¹ • (B w - A u)`. -/
theorem cutoff_projection_surjective_iff {k : ℕ} {a : ℝ} (ha : a ≠ 0)
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] E₃)
    (B : EuclideanSpace ℝ (Fin 2) →L[ℝ] E₃) :
    Surjective (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin 2) =>
      a⁻¹ • (B q.2 - A q.1)) ↔
      LinearMap.range (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E₃) ⊔
        LinearMap.range (B : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro y _
    obtain ⟨⟨u, w⟩, rfl⟩ := h y
    refine Submodule.mem_sup.mpr
      ⟨A ((-a⁻¹) • u), ⟨(-a⁻¹) • u, rfl⟩, B (a⁻¹ • w), ⟨a⁻¹ • w, rfl⟩, ?_⟩
    change A ((-a⁻¹) • u) + B (a⁻¹ • w) = a⁻¹ • (B w - A u)
    rw [map_smul, map_smul, smul_sub, neg_smul]
    abel
  · intro h y
    have hy : a • y ∈ LinearMap.range (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E₃) ⊔
        LinearMap.range (B : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) := by rw [h]; trivial
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨w, rfl⟩, heq⟩ := Submodule.mem_sup.mp hy
    have heq' : A u + B w = a • y := heq
    refine ⟨(-u, w), ?_⟩
    dsimp only
    rw [map_neg, sub_neg_eq_add, add_comm, heq', smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Assembly of the relative perturbation once arbitrarily small parameters
transverse on the positive-cutoff locus have been supplied. This lemma isolates
the generic-parameter assertion; it does not assert that Sard step. -/
theorem exists_relative_perturbation_of_good_parameters {k : ℕ} {S : Set E₃}
    {f : EuclideanSpace ℝ (Fin k) → E₃} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {W : Set (EuclideanSpace ℝ (Fin k))}
    (hfW : ∀ p ∈ W ∩ Metric.closedBall 0 1, TransverseAt S f p)
    {χ : EuclideanSpace ℝ (Fin k) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (hχone : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
      p ∉ W → χ p = 1)
    (hχzero : ∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧
      Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ V ∧ ∀ p ∈ V, χ p = 0)
    (hgood : ∀ δ > 0, ∃ v : E₃, ‖v‖ < δ ∧
      ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        0 < χ p → TransverseAt S (fun q => f q + χ q • v) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin k) → E₃, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
        ‖g p - f p‖ < ε ∧ ‖fderiv ℝ g p - fderiv ℝ f p‖ < ε) ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin k)), IsOpen V ∧
        Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ V ∧ ∀ p ∈ V, g p = f p) ∧
      ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1, TransverseAt S g p := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_cutoff_perturbation_radius hf hχ hχb hε
  obtain ⟨v, hv, htrans⟩ := hgood δ hδ
  obtain ⟨hg, hgsmall⟩ := hsmall v hv
  refine ⟨fun p => f p + χ p • v, hg, hgsmall, ?_, ?_⟩
  · obtain ⟨V, hV, hVb, hVzero⟩ := hχzero
    exact ⟨V, hV, hVb, fun p hp => by simp only [hVzero p hp, zero_smul, add_zero]⟩
  · intro p hp
    by_cases hpos : 0 < χ p
    · exact htrans p hp hpos
    · have hpzero : χ p = 0 := le_antisymm (le_of_not_gt hpos) (hχb p).1
      have hpW : p ∈ W := by
        by_contra hn
        have heq := hχone p hp hn
        rw [hpzero] at heq
        exact zero_ne_one heq
      exact (transverseAt_cutoff_perturbation_of_zero (hf.differentiable (by simp) p)
        (hχ.differentiable (by simp) p) (fun q => (hχb q).1) hpzero v).mpr (hfW p ⟨hpW, hp⟩)

-- END thm:transversality

end LiquidDrop
