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
  ∀ f : C(α, unitInterval), closure (range f)

variable {α : Type u} [TopologicalSpace α]

theorem mem_closure_range (f : C(α, unitInterval)) (x : α) : f x ∈ closure (range f) := by
  apply subset_closure
  exact mem_range_self x

def unit (x : α) : StoneCech' α := fun f => ⟨f x, mem_closure_range f x⟩

theorem continuous_unit : Continuous (unit : α → StoneCech' α) := by
  apply continuous_pi
  intro f
  refine Continuous.subtype_mk f.continuous (mem_closure_range f)

variable [CompletelyRegularSpace α] [T2Space α]

theorem unit_Injective : Function.Injective (unit : α → StoneCech' α) := by
  intro x y h
  by_contra!
  obtain ⟨U,_,hU,_,hmem,_⟩ := t2_separation this
  have hnmem : x ∉ Uᶜ := by grind
  have hcl : IsClosed Uᶜ := by simp [hU]
  obtain ⟨f, hf, hfx, hfK⟩ := CompletelyRegularSpace.completely_regular x Uᶜ hcl hnmem
  let f' : C(α, unitInterval) := { toFun := f, continuous_toFun := hf }
  unfold unit at h
  have hx : f' x = 0 := by simp [f', hfx]
  have hy : f' y = 1 := by
    have : y ∈ Uᶜ := by grind
    exact
      Eq.symm
        ((fun {i j} ↦ unitInterval.symm_inj.mp)
          (congrArg unitInterval.symm (id (EqOn.symm hfK) this)))
  have := congr_fun h f' |> Subtype.mk_eq_mk.mp
  rw [hx,hy] at this
  exact (by simp : (0 : unitInterval) ≠ 1) this

theorem range_unit_isOpen : IsOpen (range (unit : α → StoneCech' α)) := by
  refine isOpen_pi_iff.mpr ?_
  intro v hmem
  use {}, fun f => univ
  constructor
  · simp
  · simp
    sorry


theorem unit_isOpenMap : IsOpenMap (unit : α → StoneCech' α) := by
  intro U hU
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro v h
  have ⟨x, xeq⟩ : ∃x ∈ U, v = unit x := by grind
  have hcl : IsClosed Uᶜ := by simp [hU]
  have hnmem : x ∉ Uᶜ := by grind
  have ⟨f, hf, hfx, hfUc⟩ := CompletelyRegularSpace.completely_regular x Uᶜ hcl hnmem
  let f' : C(α, unitInterval) := { toFun := f, continuous_toFun := hf }
  rcases Set.eq_empty_or_nonempty Uᶜ with hemp | ⟨y, ymem⟩
  · have : U = univ := compl_empty_iff.mp hemp
    use unit '' univ
    simp [this, image_eq_range (unit : α → StoneCech' α) univ]
    constructor
    · simp_all
      sorry
    · simp_all
  have hy {y} (h : y ∉ U) : 1 = f' y := by
    simpa using id (EqOn.symm hfUc) h
  have : 1 ∈ closure (range f') := by
    rw [hy ymem]
    apply subset_closure
    exact mem_range_self y
  use (range unit) ∩ ((Function.eval f') ⁻¹' (Iio ⟨1, this⟩))
  refine ⟨?_, ?_, ?_⟩
  · intro w hmem
    simp_all only [mem_image, isClosed_compl_iff, mem_compl_iff, not_true_eq_false,
      not_false_eq_true, mem_inter_iff, mem_range, mem_preimage, Function.eval, mem_Iio]
    rcases hmem with ⟨⟨y, eq⟩, lt⟩
    rw [← eq] at lt ⊢
    use y
    apply And.intro _ rfl
    by_contra!
    simp only [unit, Subtype.mk_lt_mk] at lt
    rw [hy this] at lt
    exact lt.ne rfl
  · refine ContinuousOn.isOpen_inter_preimage ?_ ?_ isOpen_Iio
    · exact continuousOn_apply f' (range unit)
    · exact range_unit_isOpen
  · refine mem_inter ?_ ?_
    · exact mem_range_of_mem_image unit U h
    · refine mem_preimage.mpr ?_
      simp_all [Function.eval, unit, f']

theorem unit_isEmbedding : IsEmbedding (unit : α → StoneCech' α) := by
  apply IsOpenEmbedding.isEmbedding
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_unit
  · exact unit_Injective
  · exact unit_isOpenMap


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
