import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Homeomorph.Defs
import Settop.PInt

open TopologicalSpace Set

theorem stone_cech_preconnected (α : Type*) [TopologicalSpace α] [PreconnectedSpace α] :
    PreconnectedSpace (StoneCech α) := by
  apply DenseRange.preconnectedSpace denseRange_stoneCechUnit
  exact continuous_stoneCechUnit

instance : TopologicalSpace ℤ+ := ⊥
