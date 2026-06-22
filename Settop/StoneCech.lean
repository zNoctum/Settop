import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Separation.Connected
import Settop.PInt

open TopologicalSpace Set

theorem stone_cech_preconnected_iff {α : Type*} [TopologicalSpace α] :
    PreconnectedSpace α ↔ PreconnectedSpace (StoneCech α) := by
  apply Iff.intro <;> intro hI
  · apply DenseRange.preconnectedSpace denseRange_stoneCechUnit
    exact continuous_stoneCechUnit
  · rw [preconnectedSpace_iff_clopen]
    intro s hs
    have hf : Continuous s.boolIndicator := (continuous_boolIndicator_iff_isClopen s).mpr hs
    have hClopen : IsClopen (stoneCechExtend hf ⁻¹' {true}) :=
      (isClopen_discrete _).preimage (continuous_stoneCechExtend hf)
    have mem_iff a : a ∈ s ↔ stoneCechUnit a ∈ stoneCechExtend hf ⁻¹' {true} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, stoneCechExtend_stoneCechUnit hf]
      exact s.mem_iff_boolIndicator a
    rcases isClopen_iff.mp hClopen with h | h
    · left; ext a; simp only [Set.mem_empty_iff_false, iff_false]; intro ha
      have hmem := h ▸ (mem_iff a).mp ha
      exact (mem_empty_iff_false _).mp hmem
    · right; ext a; simp only [Set.mem_univ, iff_true]
      apply h ▸ (mem_iff a).mpr
      exact Set.mem_univ _

section CompactInt
instance : TopologicalSpace ℤ+ := ⊥

theorem conn1 : ¬PreconnectedSpace (StoneCech ℤ+) := by
  intro h
  haveI : DiscreteTopology ℤ+ := ⟨rfl⟩
  apply absurd (stone_cech_preconnected_iff.mpr h |>.trivial_of_discrete)
  intro h
  have : (Subtype.mk 1 (by simp) : ℤ+) ≠ Subtype.mk 2 (by simp) := by grind
  exact this (h.allEq _ _)

end CompactInt
