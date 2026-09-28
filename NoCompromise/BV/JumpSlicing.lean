import NoCompromise.BV.JumpMeasure

/-!
# Directional derivative disintegration into actual jump measures

Lebesgue-measurable sets of locally finite perimeter have locally canonical
left-continuous binary BV representatives on almost every line in any fixed unit
direction. Their nonzero jumps are finite on compact intervals. On each line,
the signed derivative measure on Borel subsets of compact intervals is exactly
the jump sum. All ambient compact C1 directional pairings are the transverse
integrals of these finite signed sums, which are Lebesgue integrable.

The formulation is a weak (tested) measure disintegration; it does not assert a
separate jointly measurable measure kernel or a total-variation kernel identity.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- A canonical left-continuous representative on a bounded open interval. Its
extension outside the interval is auxiliary and is not required to be binary. -/
structure IsBinaryBVRepresentativeOn (f g : ℝ → ℝ) (a b : ℝ) : Prop where
  boundedVariation : BoundedVariationOn g univ
  leftContinuous : ∀ t, ContinuousWithinAt g (Iic t) t
  ae_eq : f =ᵐ[volume.restrict (Ioo a b)] g
  binary : ∀ t ∈ Ioo a b, g t ∈ ({0, 1} : Set ℝ)

lemma deriv_lineSlice_real {n : ℕ} {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    deriv (fun s => φ (graphAppendN x s)) t =
      gradient (lineSlice φ x) (euclideanOneReal.symm t) 0 := by
  have he : HasFDerivAt (fun s => euclideanOneReal.symm s)
      euclideanOneReal.symm.toContinuousLinearEquiv.toContinuousLinearMap t :=
    euclideanOneReal.symm.toContinuousLinearEquiv.hasFDerivAt
  have hh := ((contDiff_lineSlice hφ x).differentiable one_ne_zero
    (euclideanOneReal.symm t)).hasFDerivAt.comp t he
  have hd := hh.hasDerivAt
  have heone : euclideanOneReal.symm (1 : ℝ) = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    simp
  rw [gradient_apply_eq_fderiv_single]
  simpa only [lineSlice, Function.comp_def, euclideanOneReal_symm_apply,
    ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, heone] using hd.deriv

lemma lineDerivativePairing_eq_real {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : EuclideanSpace ℝ (Fin n)) :
    lineDerivativePairing f φ x =
      -(∫ t : ℝ, f (graphAppendN x t) * deriv (fun s => φ (graphAppendN x s)) t) := by
  have he := euclideanOneReal.symm.measurePreserving.integral_comp
    euclideanOneReal.symm.toHomeomorph.measurableEmbedding
    (fun s => lineSlice f x s * gradient (lineSlice φ x) s 0)
  simp only [lineSlice, euclideanOneReal_symm_apply] at he
  unfold lineDerivativePairing
  simp only [lineSlice]
  rw [← he]
  simp only [deriv_lineSlice_real hφ]

lemma contDiff_lineSlice_real {n : ℕ} {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun t : ℝ => φ (graphAppendN x t)) := by
  have h := (contDiff_lineSlice hφ x).comp
    euclideanOneReal.symm.toContinuousLinearEquiv.contDiff
  change ContDiff ℝ 1 (fun t => φ (graphAppendN x (euclideanOneReal.symm t 0))) at h
  simpa only [euclideanOneReal_symm_apply] using h

lemma hasCompactSupport_lineSlice_real {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : HasCompactSupport φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun t : ℝ => φ (graphAppendN x t)) := by
  have h := (hasCompactSupport_lineSlice hφ x).comp_homeomorph
    euclideanOneReal.symm.toHomeomorph
  change HasCompactSupport (fun t => φ (graphAppendN x (euclideanOneReal.symm t 0))) at h
  simpa only [euclideanOneReal_symm_apply] using h

lemma tsupport_lineSlice_real_subset {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {a b : ℝ}
    (hφ : tsupport φ ⊆ {z | z (Fin.last n) ∈ Ioo a b})
    (x : EuclideanSpace ℝ (Fin n)) :
    tsupport (fun t : ℝ => φ (graphAppendN x t)) ⊆ Ioo a b := by
  have hcont : Continuous (fun t : ℝ => graphAppendN x t) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  intro t ht
  have hh := tsupport_comp_subset_preimage (f := fun t => graphAppendN x t) φ hcont ht
  simpa only [mem_ofPred_eq, graphAppendN_last] using hφ hh

lemma IsBinaryBVRepresentativeOn.eqOn {f g k : ℝ → ℝ} {a b : ℝ}
    (hg : IsBinaryBVRepresentativeOn f g a b) (hk : IsBinaryBVRepresentativeOn f k a b) :
    EqOn g k (Ioo a b) :=
  eqOn_Ioo_of_left_continuous_ae_eq (fun t _ => hg.leftContinuous t)
    (fun t _ => hk.leftContinuous t)
    (hg.ae_eq.symm.trans hk.ae_eq)

lemma IsBinaryBVRepresentativeOn.finite_jumps {f g : ℝ → ℝ} {a b : ℝ}
    (h : IsBinaryBVRepresentativeOn f g a b) {K : Set ℝ}
    (hK : IsCompact K) (hKU : K ⊆ Ioo a b) :
    {t ∈ K | oneDimensionalJump g t ≠ 0}.Finite :=
  finite_oneDimensionalJump_of_binary_ae h.boundedVariation h.leftContinuous
    (ae_restrict_of_forall_mem measurableSet_Ioo h.binary) hK hKU

lemma IsBinaryBVRepresentativeOn.setIntegral_eq_finsum_jumps
    {f g σ : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hg : IsBinaryBVRepresentativeOn f g a b) (hμ : IsRealBVPolar f μ σ)
    {K A : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ Ioo a b)
    (hA : MeasurableSet A) (hAK : A ⊆ K) :
    (∫ t in A, σ t ∂μ) = ∑ᶠ t : ℝ, A.indicator (oneDimensionalJump g) t :=
  hμ.setIntegral_eq_finsum_jumps hg.ae_eq hg.boundedVariation hg.leftContinuous
    hg.binary hK hKU hA hAK

lemma lineDerivativePairing_eq_finsum_jumps {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {g σ : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hg : IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) g a b)
    (hμ : IsRealBVPolar (fun t => f (graphAppendN x t)) μ σ)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ {z | z (Fin.last n) ∈ Ioo a b}) :
    lineDerivativePairing f φ x =
      ∑ᶠ t : ℝ, φ (graphAppendN x t) * oneDimensionalJump g t := by
  rw [lineDerivativePairing_eq_real hφ x]
  exact hμ.test_eq_finsum_jumps hg.ae_eq hg.boundedVariation hg.leftContinuous
    hg.binary (contDiff_lineSlice_real hφ x) (hasCompactSupport_lineSlice_real hcφ x)
    (tsupport_lineSlice_real_subset hsφ x)

/-- One family of real polar measures and locally canonical representatives works
for all bounded intervals. No pointwise regularity of the original function is used. -/
theorem IsLocallyBVOn.exists_binary_line_representatives {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (hb : ∀ z, f z ∈ ({0, 1} : Set ℝ)) :
    ∃ μ : EuclideanSpace ℝ (Fin n) → Measure ℝ,
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ,
      ∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (μ x) (σ x) ∧
        ∀ a b, IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) (g x a b) a b := by
  classical
  have hex (x : EuclideanSpace ℝ (Fin n)) :
      ∃ μ : Measure ℝ, ∃ σ : ℝ → ℝ, ∃ g : ℝ → ℝ → ℝ → ℝ,
        IsLocallyBVOn (lineSlice f x) univ →
          IsRealBVPolar (fun t => f (graphAppendN x t)) μ σ ∧
          ∀ a b, IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) (g a b) a b := by
    by_cases hx : IsLocallyBVOn (lineSlice f x) univ
    · obtain ⟨μ, σ, hμ⟩ := exists_real_bv_polar
        (f := fun t => f (graphAppendN x t)) hx
      have hex (a b : ℝ) : ∃ g : ℝ → ℝ,
          IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) g a b := by
        have hb' : ∀ᵐ t : ℝ, lineSlice f x (euclideanOneReal.symm t) ∈
            ({0, 1} : Set ℝ) := ae_of_all _ fun t => hb _
        obtain ⟨g, hg, hc, he, hgb, _⟩ := hx.exists_binary_representative_Ioo hb' a b
        refine ⟨g, hg, hc, ?_, hgb⟩
        simpa only [Function.comp_def, lineSlice, euclideanOneReal_symm_apply] using he
      choose g hg using hex
      exact ⟨μ, σ, g, fun _ => ⟨hμ, hg⟩⟩
    · exact ⟨0, fun _ => 0, fun _ _ _ => 0, fun h => (hx h).elim⟩
  choose μ σ g hg using hex
  exact ⟨μ, σ, g, hf.ae_lineSlice.mono fun x hx => hg x hx⟩

/-- Directional derivatives disintegrate, against all compact C1 tests, into the
finite jump measures of locally canonical binary representatives. The tested jump
sums are Lebesgue integrable in the transverse variable. -/
theorem IsLocallyBVOn.exists_binary_jump_disintegration {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (hb : ∀ z, f z ∈ ({0, 1} : Set ℝ)) :
    ∃ μ : EuclideanSpace ℝ (Fin n) → Measure ℝ,
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ,
      (∀ᵐ x, IsRealBVPolar (fun t => f (graphAppendN x t)) (μ x) (σ x) ∧
        ∀ a b, IsBinaryBVRepresentativeOn (fun t => f (graphAppendN x t)) (g x a b) a b) ∧
      ∀ a b (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ {z | z (Fin.last n) ∈ Ioo a b} →
        Integrable (fun x => ∑ᶠ t : ℝ, φ (graphAppendN x t) *
          oneDimensionalJump (g x a b) t) volume ∧
        -(∫ z, f z * gradient φ z (Fin.last n)) =
          ∫ x : EuclideanSpace ℝ (Fin n), ∑ᶠ t : ℝ, φ (graphAppendN x t) *
            oneDimensionalJump (g x a b) t := by
  obtain ⟨μ, σ, g, hg⟩ := hf.exists_binary_line_representatives hb
  refine ⟨μ, σ, g, hg, ?_⟩
  intro a b φ hφ hcφ hsφ
  have he : lineDerivativePairing f φ =ᵐ[volume]
      (fun x => ∑ᶠ t : ℝ, φ (graphAppendN x t) * oneDimensionalJump (g x a b) t) := by
    filter_upwards [hg] with x hx
    exact lineDerivativePairing_eq_finsum_jumps (hx.2 a b) hx.1 hφ hcφ hsφ
  have hi := locallyIntegrableOn_univ.mp hf.1
  exact ⟨(integrable_lineDerivativePairing hi hφ hcφ).congr he,
    (directional_pairing_eq_integral_lineDerivativePairing hi hφ hcφ).trans
      (integral_congr_ae he)⟩

/-- BV slicing in an arbitrary fixed unit direction. Almost every slice has its
actual real polar derivative and canonical local binary representatives. Those
representatives have finite jumps on compact subintervals, and the directional
ambient derivative is the transverse integral of their signed jump measures. -/
theorem HasLocallyFinitePerimeter.exists_jump_disintegration_direction {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      e (EuclideanSpace.single (Fin.last n) 1) = v ∧
    ∃ μ : EuclideanSpace ℝ (Fin n) → Measure ℝ,
    ∃ σ : EuclideanSpace ℝ (Fin n) → ℝ → ℝ,
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ → ℝ → ℝ → ℝ,
      (∀ᵐ x, IsRealBVPolar
          (fun t => E.indicator (fun _ => (1 : ℝ)) (e (graphAppendN x t))) (μ x) (σ x) ∧
        ∀ a b, IsBinaryBVRepresentativeOn
          (fun t => E.indicator (fun _ => (1 : ℝ)) (e (graphAppendN x t))) (g x a b) a b) ∧
      ∀ a b (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ {z | e.symm z (Fin.last n) ∈ Ioo a b} →
        Integrable (fun x => ∑ᶠ t : ℝ, φ (e (graphAppendN x t)) *
          oneDimensionalJump (g x a b) t) volume ∧
        -(∫ z, E.indicator (fun _ => (1 : ℝ)) z * fderiv ℝ φ z v) =
          ∫ x : EuclideanSpace ℝ (Fin n), ∑ᶠ t : ℝ, φ (e (graphAppendN x t)) *
            oneDimensionalJump (g x a b) t := by
  classical
  obtain ⟨e, he⟩ := exists_line_direction_frame hv
  let f := E.indicator (fun _ => (1 : ℝ))
  have hf : IsLocallyBVOn f univ := hE.isLocallyBVOn_indicator hmE univ
  have hrot := hf.comp_linearIsometryEquiv_univ e
  have hb : ∀ z, (f ∘ e) z ∈ ({0, 1} : Set ℝ) := by
    intro z
    by_cases hz : e z ∈ E <;> simp [f, hz]
  obtain ⟨μ, σ, g, hg, htest⟩ := hrot.exists_binary_jump_disintegration hb
  refine ⟨e, he, μ, σ, g, hg, ?_⟩
  intro a b φ hφ hcφ hsφ
  have hφ' : ContDiff ℝ 1 (φ ∘ e) := hφ.comp e.toContinuousLinearEquiv.contDiff
  have hcφ' : HasCompactSupport (φ ∘ e) := hcφ.comp_homeomorph e.toHomeomorph
  have hsφ' : tsupport (φ ∘ e) ⊆ {z | z (Fin.last n) ∈ Ioo a b} := by
    intro z hz
    have hh := hsφ (tsupport_comp_subset_preimage (f := e) φ e.continuous hz)
    simpa only [mem_ofPred_eq, e.symm_apply_apply] using hh
  have hsum := htest a b (φ ∘ e) hφ' hcφ' hsφ'
  refine ⟨hsum.1, ?_⟩
  have heq : lineDerivativePairing (f ∘ e) (φ ∘ e) =ᵐ[volume]
      (fun x => ∑ᶠ t : ℝ, φ (e (graphAppendN x t)) * oneDimensionalJump (g x a b) t) := by
    filter_upwards [hg] with x hx
    exact lineDerivativePairing_eq_finsum_jumps (hx.2 a b) hx.1 hφ' hcφ' hsφ'
  have hfr := frame_pairing_eq_integral_lineDerivativePairing
    (locallyIntegrableOn_univ.mp hf.1) hφ hcφ e
  rw [he] at hfr
  exact hfr.trans (integral_congr_ae heq)

end LiquidDrop
