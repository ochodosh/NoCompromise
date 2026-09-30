module

public import NoCompromise.Measure.SignedRiesz
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Local weak-star compactness

The separability statement in blueprint `lem:C0-separable` is obtained by
extending functions by zero to the one-point compactification. All topologies
on spaces of functions vanishing at infinity are the uniform norm topologies.

Uniformly locally bounded test-function functionals admit a common convergent
subsequence, also for countably many coordinate families. Signed Riesz then
represents each limit by a pair of regular measures finite on compact sets.
Locally finite signed measures are represented by positive/negative pairs;
finite vector measures are assembled in Euclidean coordinates. On each compact
set their finite signed/vector restrictions are genuine mathlib measures, and
the compactness hypothesis uses their total variation after cancellation.
Restrictions are compatible, and test integrals and variation are independent
of the representing pairs. No global finiteness is assumed for the inputs or
limits in the local compactness theorems.
-/

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ZeroAtInfty CompactlySupported ENNReal

namespace LiquidDrop

/-- A locally compact, second-countable Hausdorff space has a second-countable
one-point compactification. -/
theorem onePoint_secondCountable (X : Type*) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (OnePoint X) := by
  let K := CompactExhaustion.choice X
  let B : Set (Set (OnePoint X)) :=
    (fun V : Set X => ((↑) : X → OnePoint X) '' V) '' countableBasis X ∪
      range (fun n => (((↑) : X → OnePoint X) '' K n)ᶜ)
  have hcount : B.Countable :=
    ((countable_countableBasis X).image _).union (countable_range _)
  have hb : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro V hV
      rcases hV with hV | hV
      · obtain ⟨W, hW, rfl⟩ := hV
        exact OnePoint.isOpen_image_coe.mpr (isOpen_of_mem_countableBasis hW)
      · obtain ⟨n, rfl⟩ := hV
        exact OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro a V ha hV
      induction a using OnePoint.rec
      · obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact
          ((OnePoint.isOpen_iff_of_mem' ha).mp hV).1
        refine ⟨(((↑) : X → OnePoint X) '' K n)ᶜ, Or.inr ⟨n, rfl⟩,
          OnePoint.infty_notMem_image_coe, ?_⟩
        intro p hp
        induction p using OnePoint.rec
        · exact ha
        · rename_i x
          by_contra hx
          exact hp ⟨x, hn hx, rfl⟩
      · rename_i x
        obtain ⟨W, hW, hxW, hWV⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp
          ((hV.preimage OnePoint.continuous_coe).mem_nhds ha)
        refine ⟨((↑) : X → OnePoint X) '' W, Or.inl ⟨W, hW, rfl⟩, ⟨x, hxW, rfl⟩, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact hWV hy
  exact hb.secondCountableTopology hcount

/-- Extension by zero preserves the uniform distance. -/
theorem isometry_zeroAtInfty_toOnePoint {X : Type*} [TopologicalSpace X] [T2Space X] :
    Isometry (ZeroAtInftyContinuousMap.toOnePoint : C₀(X, ℝ) → C(OnePoint X, ℝ)) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  apply le_antisymm
  · apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro x
    induction x using OnePoint.rec
    · simp
    · rename_i x
      exact BoundedContinuousFunction.dist_coe_le_dist (f := f.toBCF) (g := g.toBCF) x
  · change dist f.toBCF g.toBCF ≤ dist f.toOnePoint g.toOnePoint
    apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    exact ContinuousMap.dist_apply_le_dist (f := f.toOnePoint) (g := g.toOnePoint) (x : OnePoint X)

/-- Blueprint `lem:C0-separable`, in the generality needed for open Euclidean domains. -/
theorem separableSpace_zeroAtInfty (X : Type*) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] : SeparableSpace C₀(X, ℝ) := by
  let := onePoint_secondCountable X
  let : SecondCountableTopology C₀(X, ℝ) :=
    isometry_zeroAtInfty_toOnePoint.isEmbedding.secondCountableTopology
  infer_instance

/-- Simultaneous weak-star subsequence extraction for countably many bounded
families of continuous linear functionals on a separable normed space. -/
theorem exists_subseq_tendsto_dual_countable {I E : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    (L : I → ℕ → StrongDual ℝ E) (C : I → ℝ)
    (hL : ∀ m j, ‖L m j‖ ≤ C m) :
    ∃ (Llim : I → StrongDual ℝ E) (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ m, ‖Llim m‖ ≤ C m) ∧
      ∀ m f, Tendsto (fun j => L m (σ j) f) atTop (𝓝 (Llim m f)) := by
  let B (m : I) := WeakDual.toStrongDual ⁻¹'
    Metric.closedBall (0 : StrongDual ℝ E) (C m)
  have hc (m : I) : IsCompact (B m) := WeakDual.isCompact_closedBall _ _
  let (m : I) : CompactSpace (B m) := isCompact_iff_compactSpace.mp (hc m)
  let (m : I) : MetrizableSpace (B m) := WeakDual.metrizable_of_isCompact ℝ E _ (hc m)
  let u (j : ℕ) (m : I) : B m :=
    ⟨StrongDual.toWeakDual (L m j), by simpa [B] using hL m j⟩
  obtain ⟨a, σ, hσ, ha⟩ := CompactSpace.tendsto_subseq u
  refine ⟨fun m => WeakDual.toStrongDual (a m).val, σ, hσ, ?_, ?_⟩
  · intro m
    simpa only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right] using (a m).property
  · intro m f
    exact ((WeakDual.eval_continuous f).comp
      (continuous_subtype_val.comp (continuous_apply m))).continuousAt.tendsto.comp ha

/-- Cutoffs for a compact exhaustion, with values in `[0,1]` and support in
the next compact set. This realizes blueprint `def:exhaustion-cutoffs`. -/
theorem exists_exhaustion_cutoffs (X : Type*) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    ∃ (K : CompactExhaustion X) (ζ : ℕ → C_c(X, ℝ)),
      (∀ m, EqOn (ζ m) 1 (K m)) ∧
      (∀ m, tsupport (ζ m) ⊆ K (m + 1)) ∧
      ∀ m x, ζ m x ∈ Icc (0 : ℝ) 1 := by
  let K := CompactExhaustion.choice X
  have h (m : ℕ) := exists_continuousMap_one_of_isCompact_subset_isOpen
    (K.isCompact m) isOpen_interior (K.subset_interior_succ m)
  choose ζ heq hc hs hb using h
  exact ⟨K, fun m => ⟨ζ m, hc m⟩, heq,
    fun m => (hs m).trans interior_subset, hb⟩

variable {X : Type*} [TopologicalSpace X]

/-- Multiplication by a compactly supported cutoff. -/
def cutoffMultiply (ζ : C_c(X, ℝ)) : C₀(X, ℝ) →ₗ[ℝ] C_c(X, ℝ) where
  toFun f :=
    { toFun := fun x => ζ x * f x
      continuous_toFun := ζ.continuous.mul f.continuous
      hasCompactSupport' := ζ.hasCompactSupport.mul_right }
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; exact mul_left_comm _ _ _

@[simp] theorem cutoffMultiply_apply (ζ : C_c(X, ℝ)) (f : C₀(X, ℝ)) (x : X) :
    cutoffMultiply ζ f x = ζ x * f x := rfl

theorem tsupport_cutoffMultiply_subset (ζ : C_c(X, ℝ)) (f : C₀(X, ℝ)) :
    tsupport (cutoffMultiply ζ f) ⊆ tsupport ζ := tsupport_mul_subset_left

theorem norm_cutoffMultiply_le (ζ : C_c(X, ℝ)) (hζ : ∀ x, ζ x ∈ Icc (0 : ℝ) 1)
    (f : C₀(X, ℝ)) : ‖(cutoffMultiply ζ f).toBoundedContinuousFunction‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro x
  change ‖ζ x * f x‖ ≤ ‖f‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hζ x).1]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hζ x).2).trans
    (f.toBCF.norm_coe_le_norm x)

theorem cutoffMultiply_eq_self (ζ f : C_c(X, ℝ))
    (hζ : EqOn ζ 1 (tsupport f)) : cutoffMultiply ζ (f : C₀(X, ℝ)) = f := by
  ext x
  by_cases hx : x ∈ tsupport f
  · simp [hζ hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Uniform bounds on every fixed compact support. -/
def IsUniformlyLocallyBounded (L : ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ j (f : C_c(X, ℝ)), tsupport f ⊆ K → |L j f| ≤ C * ‖f.toBoundedContinuousFunction‖

/-- A pointwise limit of linear functionals is linear and inherits their
uniform local bounds. -/
theorem exists_linearMap_of_pointwise_tendsto
    (L : ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ) (hL : IsUniformlyLocallyBounded L)
    (hlim : ∀ f, ∃ a : ℝ, Tendsto (fun j => L j f) atTop (𝓝 a)) :
    ∃ Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ, IsLocallyBoundedFunctional Λ ∧
      ∀ f, Tendsto (fun j => L j f) atTop (𝓝 (Λ f)) := by
  choose a ha using hlim
  let Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a
      map_add' := fun f g => tendsto_nhds_unique (ha (f + g))
        (by simpa only [map_add] using (ha f).add (ha g))
      map_smul' := fun c f => tendsto_nhds_unique (ha (c • f))
        (by simpa only [map_smul, smul_eq_mul, RingHom.id_apply] using (ha f).const_mul c) }
  refine ⟨Λ, ?_, ha⟩
  intro K hK
  obtain ⟨C, hC, hbound⟩ := hL K hK
  refine ⟨C, hC, fun f hf => ?_⟩
  exact le_of_tendsto' (ha f).abs (fun j => hbound j f hf)

/-- Simultaneous local weak-star extraction for a countable family of
sequences. In particular, this covers the finitely many components of a
vector-valued measure. -/
theorem exists_subseq_locallyBoundedFunctional_countable {I : Type*} [Countable I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (L : I → ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ i, IsUniformlyLocallyBounded (L i)) :
    ∃ (Λ : I → C_c(X, ℝ) →ₗ[ℝ] ℝ) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, IsLocallyBoundedFunctional (Λ i)) ∧
      ∀ i f, Tendsto (fun j => L i (σ j) f) atTop (𝓝 (Λ i f)) := by
  let := separableSpace_zeroAtInfty X
  obtain ⟨K, ζ, heq, _, hζ⟩ := exists_exhaustion_cutoffs X
  have hb (p : I × ℕ) := hL p.1 (tsupport (ζ p.2)) (ζ p.2).hasCompactSupport
  choose C hC hbound using hb
  let F (p : I × ℕ) (j : ℕ) : C₀(X, ℝ) →ₗ[ℝ] ℝ :=
    (L p.1 j).comp (cutoffMultiply (ζ p.2))
  have hF (p : I × ℕ) (j : ℕ) (f : C₀(X, ℝ)) : ‖F p j f‖ ≤ C p * ‖f‖ := by
    change |L p.1 j (cutoffMultiply (ζ p.2) f)| ≤ _
    exact (hbound p j _ (tsupport_cutoffMultiply_subset _ _)).trans
      (mul_le_mul_of_nonneg_left (norm_cutoffMultiply_le _ (hζ p.2) f) (hC p))
  let T (p : I × ℕ) (j : ℕ) : StrongDual ℝ C₀(X, ℝ) :=
    (F p j).mkContinuous (C p) (hF p j)
  have hT (p : I × ℕ) (j : ℕ) : ‖T p j‖ ≤ C p :=
    (F p j).mkContinuous_norm_le (hC p) (hF p j)
  obtain ⟨a, σ, hσ, _, ha⟩ := exists_subseq_tendsto_dual_countable T C hT
  have hsub (i : I) : IsUniformlyLocallyBounded (fun j => L i (σ j)) := by
    intro K hK
    obtain ⟨C, hC, hb⟩ := hL i K hK
    exact ⟨C, hC, fun j => hb (σ j)⟩
  have hlim (i : I) (f : C_c(X, ℝ)) : ∃ a : ℝ,
      Tendsto (fun j => L i (σ j) f) atTop (𝓝 a) := by
    obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
    have hcut := cutoffMultiply_eq_self (ζ m) f ((heq m).mono hm)
    refine ⟨a (i, m) (f : C₀(X, ℝ)), ?_⟩
    have h := ha (i, m) (f : C₀(X, ℝ))
    change Tendsto (fun j => L i (σ j) (cutoffMultiply (ζ m) (f : C₀(X, ℝ))))
      atTop (𝓝 (a (i, m) (f : C₀(X, ℝ)))) at h
    simpa only [hcut] using h
  have hrep (i : I) := exists_linearMap_of_pointwise_tendsto _ (hsub i) (hlim i)
  choose Λ hΛ ht using hrep
  exact ⟨Λ, σ, hσ, hΛ, ht⟩

/-- The scalar case of local weak-star extraction. -/
theorem exists_subseq_locallyBoundedFunctional [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (L : ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ) (hL : IsUniformlyLocallyBounded L) :
    ∃ (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (σ : ℕ → ℕ),
      StrictMono σ ∧ IsLocallyBoundedFunctional Λ ∧
      ∀ f, Tendsto (fun j => L (σ j) f) atTop (𝓝 (Λ f)) := by
  obtain ⟨Λ, σ, hσ, hΛ, ht⟩ := exists_subseq_locallyBoundedFunctional_countable
    (fun (_ : Unit) => L) (fun _ => hL)
  exact ⟨Λ (), σ, hσ, hΛ (), ht ()⟩

/-- The scalar local weak-star limit is represented by a difference of two
regular Borel measures, each finite on compact sets. -/
theorem exists_subseq_signed_riesz [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (L : ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ) (hL : IsUniformlyLocallyBounded L) :
    ∃ (μpos μneg : MeasureTheory.Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ μpos.Regular ∧ μneg.Regular ∧
      MeasureTheory.IsFiniteMeasureOnCompacts μpos ∧
      MeasureTheory.IsFiniteMeasureOnCompacts μneg ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun j => L (σ j) f) atTop
        (𝓝 ((∫ x, f x ∂μpos) - ∫ x, f x ∂μneg)) := by
  obtain ⟨Λ, σ, hσ, hΛ, ht⟩ := exists_subseq_locallyBoundedFunctional L hL
  obtain ⟨μpos, μneg, hp, hn, hfp, hfn, hrep⟩ := signed_riesz Λ hΛ
  exact ⟨μpos, μneg, σ, hσ, hp, hn, hfp, hfn, fun f => by rw [← hrep f]; exact ht f⟩

/-- A common subsequence and signed Riesz representations for a countable
family. For finite coordinate sets this is the vector-valued conclusion. -/
theorem exists_subseq_signed_riesz_countable {I : Type*} [Countable I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (L : I → ℕ → C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ i, IsUniformlyLocallyBounded (L i)) :
    ∃ (μpos μneg : I → MeasureTheory.Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, (μpos i).Regular ∧ (μneg i).Regular ∧
        MeasureTheory.IsFiniteMeasureOnCompacts (μpos i) ∧
        MeasureTheory.IsFiniteMeasureOnCompacts (μneg i)) ∧
      ∀ i (f : C_c(X, ℝ)), Tendsto (fun j => L i (σ j) f) atTop
        (𝓝 ((∫ x, f x ∂μpos i) - ∫ x, f x ∂μneg i)) := by
  obtain ⟨Λ, σ, hσ, hΛ, ht⟩ := exists_subseq_locallyBoundedFunctional_countable L hL
  have hrep (i : I) := signed_riesz (Λ i) (hΛ i)
  choose μpos μneg hp hn hfp hfn hrep using hrep
  exact ⟨μpos, μneg, σ, hσ, fun i => ⟨hp i, hn i, hfp i, hfn i⟩,
    fun i f => by rw [← hrep i f]; exact ht i f⟩

/-- A local mass bound controls integration against a compactly supported
continuous test function. No finiteness of the measure on the whole space
is assumed. -/
theorem norm_integral_compactlySupported_le [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (f : C_c(X, ℝ))
    {K : Set X} (hK : IsCompact K) (hf : tsupport f ⊆ K) :
    ‖∫ x, f x ∂μ‖ ≤ (μ K).toReal * ‖f.toBoundedContinuousFunction‖ := by
  let : IsFiniteMeasure (μ.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have heq : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
  rw [← heq]
  have hb := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
    (Filter.Eventually.of_forall (f.toBoundedContinuousFunction.norm_coe_le_norm))
  simpa only [measureReal_def, Measure.restrict_apply_univ, mul_comm,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using hb

/-- Differences of locally finite measures act linearly on compactly
supported continuous tests, even when both measures have infinite total mass. -/
def measurePairFunctional [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μpos μneg : Measure X)
    [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg] :
    C_c(X, ℝ) →ₗ[ℝ] ℝ :=
  (CompactlySupportedContinuousMap.integralPositiveLinearMap μpos).toLinearMap -
    (CompactlySupportedContinuousMap.integralPositiveLinearMap μneg).toLinearMap

@[simp] theorem measurePairFunctional_apply [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μpos μneg : Measure X)
    [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg] (f : C_c(X, ℝ)) :
    measurePairFunctional μpos μneg f = (∫ x, f x ∂μpos) - ∫ x, f x ∂μneg := rfl

theorem norm_measurePairFunctional_le [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μpos μneg : Measure X)
    [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg] (f : C_c(X, ℝ))
    {K : Set X} (hK : IsCompact K) (hf : tsupport f ⊆ K) :
    |measurePairFunctional μpos μneg f| ≤
      ((μpos K).toReal + (μneg K).toReal) * ‖f.toBoundedContinuousFunction‖ := by
  calc
    |measurePairFunctional μpos μneg f| ≤
        ‖∫ x, f x ∂μpos‖ + ‖∫ x, f x ∂μneg‖ := by
      rw [measurePairFunctional_apply]
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (∫ x, f x ∂μpos) (∫ x, f x ∂μneg)
    _ ≤ (μpos K).toReal * ‖f.toBoundedContinuousFunction‖ +
        (μneg K).toReal * ‖f.toBoundedContinuousFunction‖ :=
      add_le_add (norm_integral_compactlySupported_le μpos f hK hf)
        (norm_integral_compactlySupported_le μneg f hK hf)
    _ = _ := (add_mul _ _ _).symm

/-- Local weak-star compactness for a countable family of measure pairs with
uniformly bounded positive and negative masses on every compact set.
For Jordan pairs, the mass bound is precisely the total-variation bound. -/
theorem exists_subseq_measurePair_countable {I : Type*} [Countable I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : I → ℕ → Measure X)
    [∀ i j, IsFiniteMeasureOnCompacts (μpos i j)]
    [∀ i j, IsFiniteMeasureOnCompacts (μneg i j)]
    (hμ : ∀ i (K : Set X), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (μpos i j K).toReal + (μneg i j K).toReal ≤ C) :
    ∃ (νpos νneg : I → Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, (νpos i).Regular ∧ (νneg i).Regular ∧
        IsFiniteMeasureOnCompacts (νpos i) ∧ IsFiniteMeasureOnCompacts (νneg i)) ∧
      ∀ i (f : C_c(X, ℝ)), Tendsto
        (fun j => (∫ x, f x ∂μpos i (σ j)) - ∫ x, f x ∂μneg i (σ j)) atTop
        (𝓝 ((∫ x, f x ∂νpos i) - ∫ x, f x ∂νneg i)) := by
  apply exists_subseq_signed_riesz_countable
    (fun i j => measurePairFunctional (μpos i j) (μneg i j))
  intro i K hK
  obtain ⟨C, hC, hb⟩ := hμ i K hK
  refine ⟨C, hC, fun j f hf => ?_⟩
  exact (norm_measurePairFunctional_le _ _ f hK hf).trans
    (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg _))

omit [TopologicalSpace X] in
/-- The mass bound for a Jordan pair is the usual total-variation bound. -/
theorem jordanPair_mass_eq_totalVariation [MeasurableSpace X]
    (μ : SignedMeasure X) (K : Set X) :
    (μ.toJordanDecomposition.posPart K).toReal +
      (μ.toJordanDecomposition.negPart K).toReal = (μ.totalVariation K).toReal := by
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- A specialization to mathlib's finite signed measures, with the hypothesis
stated directly in terms of their total variation. The limit need only be
locally finite, so it is represented by a pair of locally finite measures. -/
theorem exists_subseq_finiteSignedMeasure_countable {I : Type*} [Countable I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : I → ℕ → SignedMeasure X)
    (hμ : ∀ i (K : Set X), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, ((μ i j).totalVariation K).toReal ≤ C) :
    ∃ (νpos νneg : I → Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, (νpos i).Regular ∧ (νneg i).Regular ∧
        IsFiniteMeasureOnCompacts (νpos i) ∧ IsFiniteMeasureOnCompacts (νneg i)) ∧
      ∀ i (f : C_c(X, ℝ)), Tendsto
        (fun j => (∫ x, f x ∂(μ i (σ j)).toJordanDecomposition.posPart) -
          ∫ x, f x ∂(μ i (σ j)).toJordanDecomposition.negPart) atTop
        (𝓝 ((∫ x, f x ∂νpos i) - ∫ x, f x ∂νneg i)) := by
  apply exists_subseq_measurePair_countable
    (fun i j => (μ i j).toJordanDecomposition.posPart)
    (fun i j => (μ i j).toJordanDecomposition.negPart)
  simpa only [jordanPair_mass_eq_totalVariation] using hμ

/-- Two finite measure pairs defining the same signed measure have the same
integrals on compactly supported continuous tests. -/
theorem measurePairFunctional_congr_of_signed_eq
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μpos μneg νpos νneg : Measure X)
    [IsFiniteMeasure μpos] [IsFiniteMeasure μneg]
    [IsFiniteMeasure νpos] [IsFiniteMeasure νneg]
    (h : μpos.toSignedMeasure - μneg.toSignedMeasure =
      νpos.toSignedMeasure - νneg.toSignedMeasure) :
    measurePairFunctional μpos μneg = measurePairFunctional νpos νneg := by
  have hsum : μpos + νneg = νpos + μneg := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    simp only [Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp h
  ext f
  simp only [measurePairFunctional_apply]
  apply sub_eq_sub_iff_add_eq_add.mpr
  calc
    (∫ x, f x ∂μpos) + ∫ x, f x ∂νneg = ∫ x, f x ∂(μpos + νneg) :=
      (integral_add_measure f.integrable f.integrable).symm
    _ = ∫ x, f x ∂(νpos + μneg) := by rw [hsum]
    _ = _ := integral_add_measure f.integrable f.integrable

/-- The total variation, rather than the sum of an arbitrary pair's masses,
controls the signed integral. This accommodates cancellation in the pair. -/
theorem norm_measurePairFunctional_le_totalVariation
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasure μpos] [IsFiniteMeasure μneg]
    (f : C_c(X, ℝ)) :
    |measurePairFunctional μpos μneg f| ≤
      ((μpos.toSignedMeasure - μneg.toSignedMeasure).totalVariation univ).toReal *
        ‖f.toBoundedContinuousFunction‖ := by
  let s := μpos.toSignedMeasure - μneg.toSignedMeasure
  have hj : μpos.toSignedMeasure - μneg.toSignedMeasure =
      s.toJordanDecomposition.posPart.toSignedMeasure -
        s.toJordanDecomposition.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s).symm
  rw [measurePairFunctional_congr_of_signed_eq μpos μneg _ _ hj, measurePairFunctional_apply]
  have hp := norm_integral_le_of_norm_le_const (μ := s.toJordanDecomposition.posPart)
    (Filter.Eventually.of_forall (f.toBoundedContinuousFunction.norm_coe_le_norm))
  have hn := norm_integral_le_of_norm_le_const (μ := s.toJordanDecomposition.negPart)
    (Filter.Eventually.of_forall (f.toBoundedContinuousFunction.norm_coe_le_norm))
  simp only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    measureReal_def] at hp hn
  have hsum := (norm_sub_le (∫ x, f x ∂s.toJordanDecomposition.posPart)
    (∫ x, f x ∂s.toJordanDecomposition.negPart)).trans (add_le_add hp hn)
  rw [← mul_add, jordanPair_mass_eq_totalVariation, mul_comm] at hsum
  exact hsum

/-- The finite signed restriction of a locally finite measure pair to a compact
set. It captures cancellation before total variation is taken. -/
def compactSignedRestriction [MeasurableSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    (K : Set X) (hK : IsCompact K) : SignedMeasure X := by
  let : IsFiniteMeasure (μpos.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (μneg.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (μpos.restrict K).toSignedMeasure - (μneg.restrict K).toSignedMeasure

/-- Total variation on a compact set for a locally finite signed measure
represented by a positive/negative pair. Both total masses may be infinite. -/
def compactTotalVariation [MeasurableSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    (K : Set X) (hK : IsCompact K) : ℝ≥0∞ :=
  (compactSignedRestriction μpos μneg K hK).totalVariation univ

theorem compactTotalVariation_ne_top [MeasurableSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    (K : Set X) (hK : IsCompact K) : compactTotalVariation μpos μneg K hK ≠ ⊤ :=
  measure_ne_top _ _

/-- The required local bound with the genuine variation of the compact
restriction; there is no bound on the separate positive and negative masses. -/
theorem norm_measurePairFunctional_le_compactTotalVariation
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    (f : C_c(X, ℝ)) {K : Set X} (hK : IsCompact K) (hf : tsupport f ⊆ K) :
    |measurePairFunctional μpos μneg f| ≤
      (compactTotalVariation μpos μneg K hK).toReal * ‖f.toBoundedContinuousFunction‖ := by
  let : IsFiniteMeasure (μpos.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (μneg.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have heq (μ : Measure X) : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
  have h := norm_measurePairFunctional_le_totalVariation (μpos.restrict K) (μneg.restrict K) f
  simp only [measurePairFunctional_apply, heq] at h
  exact h

/-- Local weak-star compactness under bounds on total variation on compact
sets, for arbitrary locally finite measure pairs and countably many coordinates. -/
theorem exists_subseq_of_compactTotalVariation_countable {I : Type*} [Countable I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : I → ℕ → Measure X)
    [∀ i j, IsFiniteMeasureOnCompacts (μpos i j)]
    [∀ i j, IsFiniteMeasureOnCompacts (μneg i j)]
    (hμ : ∀ i (K : Set X) (hK : IsCompact K), ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (compactTotalVariation (μpos i j) (μneg i j) K hK).toReal ≤ C) :
    ∃ (νpos νneg : I → Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, (νpos i).Regular ∧ (νneg i).Regular ∧
        IsFiniteMeasureOnCompacts (νpos i) ∧ IsFiniteMeasureOnCompacts (νneg i)) ∧
      ∀ i (f : C_c(X, ℝ)), Tendsto
        (fun j => (∫ x, f x ∂μpos i (σ j)) - ∫ x, f x ∂μneg i (σ j)) atTop
        (𝓝 ((∫ x, f x ∂νpos i) - ∫ x, f x ∂νneg i)) := by
  apply exists_subseq_signed_riesz_countable
    (fun i j => measurePairFunctional (μpos i j) (μneg i j))
  intro i K hK
  obtain ⟨C, hC, hb⟩ := hμ i K hK
  refine ⟨C, hC, fun j f hf => ?_⟩
  exact (norm_measurePairFunctional_le_compactTotalVariation _ _ f hK hf).trans
    (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg _))

/-- Compact restriction is compatible with further restriction. -/
theorem compactSignedRestriction_restrict [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    {K K' : Set X} (hK : IsCompact K) (hK' : IsCompact K') (hsub : K' ⊆ K) :
    (compactSignedRestriction μpos μneg K hK).restrict K' =
      compactSignedRestriction μpos μneg K' hK' := by
  let : IsFiniteMeasure (μpos.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (μneg.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (μpos.restrict K') := isFiniteMeasure_restrict.mpr hK'.measure_ne_top
  let : IsFiniteMeasure (μneg.restrict K') := isFiniteMeasure_restrict.mpr hK'.measure_ne_top
  unfold compactSignedRestriction
  rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hK'.measurableSet,
    VectorMeasure.restrict_toSignedMeasure hK'.measurableSet]
  apply congrArg₂ (· - ·)
  · apply Measure.toSignedMeasure_congr
    rw [Measure.restrict_restrict hK'.measurableSet, inter_eq_left.mpr hsub]
  · apply Measure.toSignedMeasure_congr
    rw [Measure.restrict_restrict hK'.measurableSet, inter_eq_left.mpr hsub]

@[simp] theorem compactTotalVariation_self [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (K : Set X) (hK : IsCompact K) :
    compactTotalVariation μ μ K hK = 0 := by
  simp [compactTotalVariation, compactSignedRestriction, SignedMeasure.totalVariation_zero]

/-- Assemble finitely many signed coordinates into a genuine Euclidean-valued
vector measure. -/
def vectorMeasureOfCoordinates {I : Type*} [Fintype I] [MeasurableSpace X]
    (s : I → SignedMeasure X) : VectorMeasure X (EuclideanSpace ℝ I) := by
  let v : VectorMeasure X (I → ℝ) :=
    { measureOf' := fun A i => s i A
      empty' := by ext i; exact (s i).empty
      not_measurable' := by intro A h; ext i; exact (s i).not_measurable h
      m_iUnion' := by
        intro f hm hd
        apply tendsto_pi_nhds.mpr
        intro i
        simpa only [HasSum, Finset.sum_apply] using (s i).m_iUnion hm hd }
  exact v.mapRange (WithLp.linearEquiv 2 ℝ (I → ℝ)).symm.toAddMonoidHom
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ))

omit [TopologicalSpace X] in
@[simp] theorem vectorMeasureOfCoordinates_apply {I : Type*} [Fintype I] [MeasurableSpace X]
    (s : I → SignedMeasure X) (A : Set X) (i : I) :
    vectorMeasureOfCoordinates s A i = s i A := rfl

omit [TopologicalSpace X] in
/-- Coordinate total variation is bounded by Euclidean vector variation. -/
theorem coordinate_totalVariation_le {I : Type*} [Fintype I] [MeasurableSpace X]
    (s : I → SignedMeasure X) (i : I) :
    (s i).totalVariation ≤ (vectorMeasureOfCoordinates s).variation := by
  rw [SignedMeasure.totalVariation_eq_variation]
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro A _
  exact (PiLp.enorm_apply_le (vectorMeasureOfCoordinates s A) i).trans
    ((vectorMeasureOfCoordinates s).enorm_measure_le_variation A)

omit [TopologicalSpace X] in
/-- The converse estimate by the sum of coordinate variations guarantees
finiteness on each compact restriction. -/
theorem vectorMeasureOfCoordinates_variation_le {I : Type*} [Fintype I] [MeasurableSpace X]
    (s : I → SignedMeasure X) :
    (vectorMeasureOfCoordinates s).variation ≤ ∑ i, (s i).totalVariation := by
  classical
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro A _
  let e : I → EuclideanSpace ℝ I := fun i => PiLp.single 2 i (s i A)
  have heq : (∑ i, e i) = vectorMeasureOfCoordinates s A := by
    ext i
    simp [e]
  have hnorm (i : I) : ‖e i‖ₑ = ‖s i A‖ₑ := by simp [e, enorm_eq_nnnorm]
  calc
    ‖vectorMeasureOfCoordinates s A‖ₑ = ‖∑ i, e i‖ₑ := by rw [heq]
    _ ≤ ∑ i, ‖e i‖ₑ := enorm_sum_le Finset.univ e
    _ = ∑ i, ‖s i A‖ₑ := Finset.sum_congr rfl (fun i _ => hnorm i)
    _ ≤ ∑ i, (s i).totalVariation A := Finset.sum_le_sum fun i _ =>
      (s i).enorm_le_totalVariation A
    _ = (∑ i, (s i).totalVariation) A := (Measure.finsetSum_apply _ _ _).symm

/-- The finite Euclidean vector restriction of a locally finite coordinate pair. -/
def compactVectorRestriction {I : Type*} [Fintype I] [MeasurableSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    (K : Set X) (hK : IsCompact K) : VectorMeasure X (EuclideanSpace ℝ I) :=
  vectorMeasureOfCoordinates (fun i => compactSignedRestriction (μpos i) (μneg i) K hK)

omit [TopologicalSpace X] in
/-- Coordinate assembly commutes with restriction of vector measures. -/
theorem vectorMeasureOfCoordinates_restrict {I : Type*} [Fintype I] [MeasurableSpace X]
    (s : I → SignedMeasure X) {K : Set X} (hK : MeasurableSet K) :
    vectorMeasureOfCoordinates (fun i => (s i).restrict K) =
      (vectorMeasureOfCoordinates s).restrict K := by
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.restrict_apply _ hK hA]
  ext i
  exact VectorMeasure.restrict_apply (s i) hK hA

/-- The finite vector restrictions form a compatible local vector measure. -/
theorem compactVectorRestriction_restrict {I : Type*} [Fintype I] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    {K K' : Set X} (hK : IsCompact K) (hK' : IsCompact K') (hsub : K' ⊆ K) :
    (compactVectorRestriction μpos μneg K hK).restrict K' =
      compactVectorRestriction μpos μneg K' hK' := by
  unfold compactVectorRestriction
  rw [← vectorMeasureOfCoordinates_restrict _ hK'.measurableSet]
  congr 1
  funext i
  exact compactSignedRestriction_restrict (μpos i) (μneg i) hK hK' hsub

/-- For finite input measures the compact restriction is the ordinary signed
measure restriction. -/
theorem compactSignedRestriction_of_finite [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : Measure X) [IsFiniteMeasure μpos] [IsFiniteMeasure μneg]
    (K : Set X) (hK : IsCompact K) :
    compactSignedRestriction μpos μneg K hK =
      (μpos.toSignedMeasure - μneg.toSignedMeasure).restrict K := by
  rw [VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure hK.measurableSet,
    VectorMeasure.restrict_toSignedMeasure hK.measurableSet]
  rfl

/-- Euclidean total variation of the finite vector restriction to a compact set. -/
def compactVectorTotalVariation {I : Type*} [Fintype I] [MeasurableSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    (K : Set X) (hK : IsCompact K) : ℝ≥0∞ :=
  (compactVectorRestriction μpos μneg K hK).variation univ

theorem compactVectorTotalVariation_ne_top {I : Type*} [Fintype I] [MeasurableSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    (K : Set X) (hK : IsCompact K) : compactVectorTotalVariation μpos μneg K hK ≠ ⊤ := by
  have h := vectorMeasureOfCoordinates_variation_le
    (fun i => compactSignedRestriction (μpos i) (μneg i) K hK)
  exact ne_top_of_le_ne_top (measure_ne_top _ univ) (h univ)

theorem compactTotalVariation_le_vector {I : Type*} [Fintype I] [MeasurableSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    (K : Set X) (hK : IsCompact K) (i : I) :
    compactTotalVariation (μpos i) (μneg i) K hK ≤ compactVectorTotalVariation μpos μneg K hK :=
  coordinate_totalVariation_le (fun i => compactSignedRestriction (μpos i) (μneg i) K hK) i univ

/-- On finite measure pairs the local vector variation is exactly the usual
Euclidean vector variation evaluated on the compact set. -/
theorem compactVectorTotalVariation_of_finite {I : Type*} [Fintype I] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : I → Measure X)
    [∀ i, IsFiniteMeasure (μpos i)] [∀ i, IsFiniteMeasure (μneg i)]
    (K : Set X) (hK : IsCompact K) :
    compactVectorTotalVariation μpos μneg K hK =
      (vectorMeasureOfCoordinates (fun i => (μpos i).toSignedMeasure -
        (μneg i).toSignedMeasure)).variation K := by
  unfold compactVectorTotalVariation compactVectorRestriction
  simp_rw [compactSignedRestriction_of_finite]
  rw [vectorMeasureOfCoordinates_restrict _ hK.measurableSet,
    VectorMeasure.variation_restrict hK.measurableSet, Measure.restrict_apply_univ]

/-- Test integration is independent of the chosen locally finite positive/negative
representation whenever the finite signed restrictions agree. -/
theorem measurePairFunctional_congr_of_compactSigned_eq
    [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μpos μneg νpos νneg : Measure X)
    [IsFiniteMeasureOnCompacts μpos] [IsFiniteMeasureOnCompacts μneg]
    [IsFiniteMeasureOnCompacts νpos] [IsFiniteMeasureOnCompacts νneg]
    (h : ∀ (K : Set X) (hK : IsCompact K),
      compactSignedRestriction μpos μneg K hK = compactSignedRestriction νpos νneg K hK) :
    measurePairFunctional μpos μneg = measurePairFunctional νpos νneg := by
  ext f
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  let : IsFiniteMeasure (μpos.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (μneg.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (νpos.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (νneg.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have heq (μ : Measure X) : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hx => image_eq_zero_of_notMem_tsupport hx
  have hf := congrArg (fun Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ => Λ f)
    (measurePairFunctional_congr_of_signed_eq (μpos.restrict K) (μneg.restrict K)
      (νpos.restrict K) (νneg.restrict K) (h K hK))
  simpa only [measurePairFunctional_apply, heq] using hf

/-- Euclidean local variation is likewise independent of those representations. -/
theorem compactVectorTotalVariation_congr {I : Type*} [Fintype I] [MeasurableSpace X]
    (μpos μneg νpos νneg : I → Measure X)
    [∀ i, IsFiniteMeasureOnCompacts (μpos i)] [∀ i, IsFiniteMeasureOnCompacts (μneg i)]
    [∀ i, IsFiniteMeasureOnCompacts (νpos i)] [∀ i, IsFiniteMeasureOnCompacts (νneg i)]
    (K : Set X) (hK : IsCompact K)
    (h : ∀ i, compactSignedRestriction (μpos i) (μneg i) K hK =
      compactSignedRestriction (νpos i) (νneg i) K hK) :
    compactVectorTotalVariation μpos μneg K hK = compactVectorTotalVariation νpos νneg K hK := by
  unfold compactVectorTotalVariation compactVectorRestriction
  rw [show (fun i => compactSignedRestriction (μpos i) (μneg i) K hK) =
    (fun i => compactSignedRestriction (νpos i) (νneg i) K hK) from funext h]

/-- Blueprint `thm:weak-star-compactness`, in finite Euclidean coordinates.
A locally finite vector measure is represented by locally finite positive and
negative measures for each coordinate; variation is that of its actual finite
Euclidean vector restriction to a compact set. -/
theorem exists_subseq_localVectorMeasure {I : Type*} [Fintype I]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    (μpos μneg : I → ℕ → Measure X)
    [∀ i j, IsFiniteMeasureOnCompacts (μpos i j)]
    [∀ i j, IsFiniteMeasureOnCompacts (μneg i j)]
    (hμ : ∀ (K : Set X) (hK : IsCompact K), ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (compactVectorTotalVariation (fun i => μpos i j) (fun i => μneg i j) K hK).toReal ≤ C) :
    ∃ (νpos νneg : I → Measure X) (σ : ℕ → ℕ),
      StrictMono σ ∧ (∀ i, (νpos i).Regular ∧ (νneg i).Regular ∧
        IsFiniteMeasureOnCompacts (νpos i) ∧ IsFiniteMeasureOnCompacts (νneg i)) ∧
      ∀ f : C_c(X, ℝ), Tendsto
        (fun j => WithLp.toLp 2 (fun i => (∫ x, f x ∂μpos i (σ j)) - ∫ x, f x ∂μneg i (σ j))) atTop
        (𝓝 (WithLp.toLp 2 (fun i => (∫ x, f x ∂νpos i) - ∫ x, f x ∂νneg i))) := by
  have hb (i : I) (K : Set X) (hK : IsCompact K) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (compactTotalVariation (μpos i j) (μneg i j) K hK).toReal ≤ C := by
    obtain ⟨C, hC, hc⟩ := hμ K hK
    refine ⟨C, hC, fun j => ?_⟩
    have hfin := compactVectorTotalVariation_ne_top
      (fun i => μpos i j) (fun i => μneg i j) K hK
    have hle := compactTotalVariation_le_vector
      (fun i => μpos i j) (fun i => μneg i j) K hK i
    exact (ENNReal.toReal_mono hfin hle).trans (hc j)
  obtain ⟨νpos, νneg, σ, hσ, hν, ht⟩ :=
    exists_subseq_of_compactTotalVariation_countable μpos μneg hb
  refine ⟨νpos, νneg, σ, hσ, hν, fun f => ?_⟩
  exact (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun i => ht i f)

end LiquidDrop
