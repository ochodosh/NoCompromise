import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-!
# Compact null sets under local weak-star convergence

Outer regularity and a compactly supported Urysohn majorant show that compact
null sets have vanishing mass under convergence on compact continuous tests.
The approximating measures need only be locally finite eventually.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- A compact null set has vanishing real mass under local weak-star convergence. -/
theorem tendsto_real_compact_null_of_compact_test_convergence {n : ℕ} {α : Type*}
    {l : Filter α} (μs : α → Measure (EuclideanSpace ℝ (Fin n)))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.OuterRegular]
    [IsFiniteMeasureOnCompacts μ]
    (hfin : ∀ᶠ a in l, IsFiniteMeasureOnCompacts (μs a))
    (ht : ∀ f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ,
      Tendsto (fun a => ∫ y, f y ∂μs a) l (𝓝 (∫ y, f y ∂μ)))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hnull : μ K = 0) :
    Tendsto (fun a => (μs a).real K) l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun _ => hb.trans_le ENNReal.toReal_nonneg
  · intro b hb
    obtain ⟨O, hKO, hO, hμO⟩ := K.exists_isOpen_lt_of_lt (μ := μ) (ENNReal.ofReal b)
      (by rw [hnull]; exact ENNReal.ofReal_pos.mpr hb)
    obtain ⟨f, hfK, hfO, hfc, hfb⟩ := exists_continuous_one_zero_of_isCompact
      hK hO.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKO)
    have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport hfc
    have hO_fin : μ O ≠ ∞ := (hμO.trans_le le_top).ne
    have hint : (∫ y, f y ∂μ) < b := by
      calc
        _ = ∫ y in O, f y ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => hfO hy)).symm
        _ ≤ ∫ _y in O, (1 : ℝ) ∂μ :=
          integral_mono_ae hfi.integrableOn (integrableOn_const hO_fin)
            (Eventually.of_forall fun y => (hfb y).2)
        _ = μ.real O := by simp
        _ < b := (ENNReal.toReal_lt_of_lt_ofReal hμO)
    filter_upwards [(ht ⟨f, hfc⟩).eventually (Iio_mem_nhds hint), hfin] with a ha hfa
    let := hfa
    have hi : Integrable f (μs a) := f.continuous.integrable_of_hasCompactSupport hfc
    have hmass : (μs a).real K ≤ ∫ y, f y ∂μs a := by
      calc
        _ = ∫ y in K, f y ∂μs a := by
          rw [show (∫ y in K, f y ∂μs a) = ∫ _y in K, (1 : ℝ) ∂μs a from
            setIntegral_congr_fun hK.measurableSet (fun y hy => hfK hy)]
          simp
        _ ≤ ∫ y, f y ∂μs a :=
          setIntegral_le_integral hi (Eventually.of_forall fun y => (hfb y).1)
    exact hmass.trans_lt ha

end LiquidDrop
