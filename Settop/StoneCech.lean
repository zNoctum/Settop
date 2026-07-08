import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions

open TopologicalSpace Topology Set

abbrev StoneCech' (α : Type u) [TopologicalSpace α] :=
  ∀ f : C(α, unitInterval), unitInterval

variable {α : Type u} [TopologicalSpace α]

theorem mem_closure_range (f : C(α, unitInterval)) (x : α) : f x ∈ closure (range f) := by
  apply subset_closure
  exact mem_range_self x

def unit (x : α) : StoneCech' α := fun f => f x

theorem continuous_unit : Continuous (unit : α → StoneCech' α) := by
  apply continuous_pi
  intro f
  simp [unit, ContinuousMap.continuous f]

variable [CompletelyRegularSpace α]

theorem exists_seperating_index {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : C(α, unitInterval), f x = 0 ∧ EqOn f 1 Uᶜ := by
  have ⟨f, hf, hfx, hfUc⟩ := CompletelyRegularSpace.completely_regular_isOpen x U hU hx
  use { toFun := f, continuous_toFun := hf }
  simpa using And.intro hfx hfUc

theorem unit_isInducing : IsInducing (unit : α → StoneCech' α) := by
  refine (isInducing_iff unit).mpr ?_
  refine Eq.symm (TopologicalSpace.ext ?_)
  ext O
  constructor
  · rw [isOpen_induced_iff]
    rintro ⟨U, hU, pre⟩
    rw [← pre]
    exact Continuous.isOpen_preimage continuous_unit U hU
  · intro hO
    apply (@isOpen_iff_forall_mem_open _ (induced unit Pi.topologicalSpace) O).mpr
    intro x hx
    have ⟨f, hfx, hfOc⟩ := exists_seperating_index hO hx
    use f ⁻¹' (Iio 1)
    refine ⟨?_,?_,?_⟩
    · refine preimage_subset_iff.mpr ?_
      intro y hy
      by_contra!
      have : f y = 1 := by
        simpa using hfOc this
      rw [this] at hy
      grind
    · apply isOpen_induced_iff.mpr
      use (Function.eval f) ⁻¹' Iio 1
      constructor
      · refine Continuous.isOpen_preimage ?_ (Iio 1) ?_
        · exact continuous_apply f
        · exact isOpen_Iio
      · exact Eq.symm (preimage_congr (congrFun rfl))
    · simp [hfx]

variable [T2Space α]

theorem unit_Injective : Function.Injective (unit : α → StoneCech' α) := by
  intro x y h
  by_contra!
  obtain ⟨U,_,hU,_,hmem,_⟩ := t2_separation this
  have ⟨f, hfx, hfUc⟩ := exists_seperating_index hU hmem
  unfold unit at h
  have hx : f x = 0 := by simp [hfx]
  have hy : f y = 1 := by
    simpa using hfUc (by grind)
  have := hx ▸ hy ▸ congr_fun h f
  exact (by simp : (0 : unitInterval) ≠ 1) this

theorem unit_isEmbedding : IsEmbedding (unit : α → StoneCech' α) := by
  refine (isEmbedding_iff unit).mpr ?_
  exact ⟨unit_isInducing, unit_Injective⟩

section Extension

variable {β : Type u} [TopologicalSpace β] [T2Space β]
variable {g : α → β} (hg : Continuous g)

def stoneCechExtend' [Nonempty α] : StoneCech' α → β := by
  let F (x : StoneCech' α) : StoneCech' β := fun f => x { toFun := f ∘ g }
  have hi := (unit_Injective (α := α)).leftInverse
  exact hi.choose ∘ F
  sorry

end Extension
/-
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
instance : TopologicalSpace ℤ := ⊥

theorem conn1 : ¬PreconnectedSpace (StoneCech ℤ) := by
  intro h
  haveI : DiscreteTopology ℤ := ⟨rfl⟩
  apply absurd (stone_cech_preconnected_iff.mpr h |>.trivial_of_discrete)
  intro h
  exact (by grind : (0 : ℤ) ≠ 1) (h.allEq 0 1)

end CompactInt
-/
