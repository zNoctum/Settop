import Mathlib.Topology.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions

import Settop.StoneCechEquiv

open TopologicalSpace Topology Set

/-- `I ^ C(α, I)` the product of copies of the unit interval indexed by the continuous
maps `α → I`. The Stone–Čech compactification is a closed subspace of it. -/
abbrev IntervalCube (α : Type u) [TopologicalSpace α] :=
  C(α, unitInterval) → unitInterval

variable {α : Type u} [TopologicalSpace α]

/-- The evaluation map `h_α : α → I ^ C(α, I)`, `x ↦ (f x)_{f ∈ C(α, I)}`. -/
def intervalCubeUnit (x : α) : IntervalCube α := fun f => f x

/-- `intervalCubeUnit` is continuous, being a product of continuous maps. -/
theorem continuous_intervalCubeUnit : Continuous (intervalCubeUnit : α → IntervalCube α) := by
  apply continuous_pi
  intro f
  simp [intervalCubeUnit, ContinuousMap.continuous f]


/-- The map `F : I ^ C(α, I) → I ^ C(β, I)` induced by a continuous `g : α → β`, reindexing a
point by precomposition with `g`. It restricts to the compactifications. -/
def intervalCubeMap {β : Type u} [TopologicalSpace β] {g : α → β} (hg : Continuous g) (x : IntervalCube α) :
    IntervalCube β :=
  fun f => x { toFun := f ∘ g }

/-- The product-space construction of the Stone–Čech compactification:
`βα = closure (range h_α)` inside `I ^ C(α, I)`. -/
abbrev ProdStoneCech (α : Type u) [TopologicalSpace α] :=
  closure (range (intervalCubeUnit : α → IntervalCube α))

/-- `βα` is compact, being a closed subspace of the cube, which is compact by Tychonoff. -/
instance : CompactSpace (ProdStoneCech α) := by
  unfold ProdStoneCech intervalCubeUnit
  apply isCompact_iff_compactSpace.mp
  apply exists_isCompact_superset_iff.mp
  exact ⟨univ, CompactSpace.isCompact_univ, by simp⟩

/-- The unit `α → βα`, i.e. `intervalCubeUnit` with its codomain restricted to the closure of its
range. -/
abbrev ProdStoneCech.unit (x : α) : ProdStoneCech α :=
  ⟨intervalCubeUnit x, by rw [ProdStoneCech]; exact subset_closure <| mem_range_self _ ⟩

/-- Every value of a map lies in the closure of its range. -/
theorem mem_closure_range_self (f : C(α, unitInterval)) (x : α) : f x ∈ closure (range f) := by
  apply subset_closure
  exact mem_range_self x

/-- The unit is continuous. -/
theorem ProdStoneCech.continuous_unit : Continuous (ProdStoneCech.unit : α → ProdStoneCech α) :=
  Continuous.subtype_mk continuous_intervalCubeUnit _

section homeo

variable [T2Space α] [CompactSpace α]

/-- Complete regularity: a point of an open set can be separated from the complement by a
continuous `α → I` vanishing at the point and constantly `1` outside the set. -/
theorem exists_continuous_zero_eqOn_one_compl {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : C(α, unitInterval), f x = 0 ∧ EqOn f 1 Uᶜ := by
  haveI h : CompletelyRegularSpace α := inferInstance
  have ⟨f, hf, hfx, hfuc⟩ := CompletelyRegularSpace.completely_regular_isOpen x U hU hx
  use ⟨f, hf⟩
  simpa using ⟨hfx, hfuc⟩

/-- On a compact Hausdorff space the unit is injective: two distinct points are separated by
some `f ∈ C(α, I)` due to the complete regularity of `α`. -/
theorem ProdStoneCech.unit_injective : Function.Injective (ProdStoneCech.unit : α → ProdStoneCech α) := by
  intro x y h
  by_contra hneq
  have ⟨U,_,hU,_,hmem,_⟩ := t2_separation hneq
  have ⟨f, hfx, hfUc⟩ := exists_continuous_zero_eqOn_one_compl hU hmem
  unfold ProdStoneCech.unit at h
  have hx : f x = 0 := by simp [hfx]
  have hy : f y = 1 := by
    simpa using hfUc (by grind)
  have := congr_fun (Subtype.mk_eq_mk.mp h) f
  simp [hx,hy,intervalCubeUnit] at this

/-- For compact Hausdorff `α` the unit is a homeomorphism onto `βα`: it is injective and its
range is already closed, being compact. -/
theorem ProdStoneCech.isHomeomorph_unit : IsHomeomorph (ProdStoneCech.unit : α → ProdStoneCech α) := by
  refine (isHomeomorph_iff_continuous_bijective).mpr
    ⟨ProdStoneCech.continuous_unit, ProdStoneCech.unit_injective, ?_⟩
  apply Set.range_eq_univ.mp
  refine eq_univ_of_image_val_eq ?_
  unfold ProdStoneCech.unit ProdStoneCech
  rw [← range_comp']
  conv => lhs; rhs; intro; rw [Subtype.coe_mk]
  refine Eq.symm (IsClosed.closure_eq ?_)
  refine IsCompact.isClosed ?_
  refine isCompact_range continuous_intervalCubeUnit

end homeo

/-- The unit has dense range, by construction of `βα` as the closure of that range. -/
theorem ProdStoneCech.denseRange_unit : DenseRange (ProdStoneCech.unit : α → ProdStoneCech α) := by
  refine denseRange_iff_closure_range.mpr ?_
  rw [eq_univ_iff_forall]
  intro ⟨x,h⟩
  have h : closure (Subtype.val '' range (ProdStoneCech.unit : α → ProdStoneCech α))
      = closure (range intervalCubeUnit) := by
    apply congr_arg
    rw [← range_comp']
  simpa [ProdStoneCech, closure_subtype, h]

variable {β : Type v} [TopologicalSpace β] [T2Space β]
variable {g : α → β} (hg : Continuous g)

/-- The proof of the uniqueness of a extension of a continuous map `f : α → β` into a
compact Hausdorff space `β`. -/
theorem ProdStoneCech.hom_ext {g₁ g₂ : ProdStoneCech α → β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ ProdStoneCech.unit = g₂ ∘ ProdStoneCech.unit) : g₁ = g₂ := by
  apply h₁.ext_on ProdStoneCech.denseRange_unit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

section Extension

variable {β : Type u} [TopologicalSpace β] [T2Space β] [CompactSpace β]
variable {g : α → β} (hg : Continuous g)

/-- `intervalCubeMap` maps `βα` into `ββ`, so it can be restricted to the compactifications. -/
theorem ProdStoneCech.mapsTo_intervalCubeMap :
    Set.MapsTo (intervalCubeMap hg) (ProdStoneCech α) (ProdStoneCech β) := by
  refine MapsTo.closure ?_ ?_
  · refine mapsTo_range_iff.mpr ?_
    intro x
    exact mem_range_self (g x)
  · apply continuous_pi
    intro f
    exact continuous_apply ({ toFun := f ∘ g } : C(α,unitInterval))

/-- The lifted function `G : βα → ββ` of a continuous `g : α → β`, i.e. `intervalCubeMap`
restricted to the compactifications. -/
noncomputable def ProdStoneCech.map : ProdStoneCech α → ProdStoneCech β :=
  Set.MapsTo.restrict (intervalCubeMap hg) (ProdStoneCech α) (ProdStoneCech β)
    (ProdStoneCech.mapsTo_intervalCubeMap hg)

/-- Naturality of the unit: `unit ∘ g = βg ∘ unit`. -/
theorem ProdStoneCech.unit_naturality :
    ProdStoneCech.unit ∘ g = (ProdStoneCech.map hg) ∘ ProdStoneCech.unit :=
  rfl

/-- The extension of a continuous `g : α → β` into a compact Hausdorff space `β`, obtained as
`G` followed by the inverse of the unit of `β` (a homeomorphism, since `β` is compact
Hausdorff). -/
noncomputable def ProdStoneCech.extend [h : Nonempty α] : ProdStoneCech α → β := by
  have : Nonempty β := by by_contra!; exact this.elim (g h.some)
  exact ProdStoneCech.isHomeomorph_unit.homeomorph.symm ∘ (ProdStoneCech.map hg)

/-- The extension is continuous. -/
theorem ProdStoneCech.continuous_extend [h : Nonempty α] :
    Continuous (ProdStoneCech.extend hg) := by
  have : Nonempty β := by by_contra!; exact this.elim (g h.some)
  unfold ProdStoneCech.extend ProdStoneCech.map
  refine Continuous.comp ?_ ?_
  · exact ProdStoneCech.isHomeomorph_unit.homeomorph.symm.continuous
  refine Continuous.restrict (ProdStoneCech.mapsTo_intervalCubeMap hg) ?_
  refine continuous_pi fun f => ?_
  apply continuous_apply

/-- The extension of `g` is a extension in the sense of a Stone–Čech compactification. -/
theorem ProdStoneCech.extend_comp_unit [h : Nonempty α] :
    (ProdStoneCech.extend hg) ∘ ProdStoneCech.unit = g := by
  have : Nonempty β := by by_contra!; exact this.elim (g h.some)
  ext x
  unfold ProdStoneCech.extend
  have : (ProdStoneCech.unit : β → _) = ProdStoneCech.isHomeomorph_unit.homeomorph := rfl
  rw [Function.comp_assoc, ← ProdStoneCech.unit_naturality hg]
  conv => lhs; lhs; rw [this]
  rw [← Function.comp_assoc]
  simp

end Extension

/-- The product-space construction is a Stone–Čech compactification in the sense of
`Compactification` therefore homeomorphic to every other one by `Compactification.homeomorph`. -/
noncomputable instance {α : Type*} [TopologicalSpace α] [Nonempty α] :
    Compactification α (ProdStoneCech α) where
  unit := ⟨ProdStoneCech.unit, ProdStoneCech.continuous_unit⟩
  extend g := ⟨ProdStoneCech.extend (map_continuous g),
    ProdStoneCech.continuous_extend (map_continuous g)⟩
  extend_comp g := by
    ext x; simpa using congr_fun (ProdStoneCech.extend_comp_unit (map_continuous g)) x
  hom_ext {γ} _ _ _ g₁ g₂ h := by
    have : g₁ ∘ ProdStoneCech.unit = g₂ ∘ ProdStoneCech.unit := by
      ext x; simpa using ContinuousMap.congr_fun h x
    simpa using ProdStoneCech.hom_ext (map_continuous g₁) (map_continuous g₂) this
