import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.Data.Countable.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Prod
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Bases
import Mathlib.Topology.NatEmbedding
import Settop.Card

open Cardinal Set Topology

/-- If `α` has the discrete topology then `Ultrafilter α` is projective in the category of compact
Hausdorff spaces, this is interesting as projective objects are extremally disconnected:
closures of open sets are open. -/
theorem Ultrafilter.projective : CompactT2.Projective (Ultrafilter α) := by
  intro X Y _ _ _ _ _ _ f g hf hg hsurj
  letI : TopologicalSpace α := ⊥
  let h : α → X := (hsurj · |>.choose) ∘ f ∘ pure
  refine ⟨Ultrafilter.extend h, continuous_ultrafilter_extend h, ?_⟩
  have hgh : Continuous (g ∘ Ultrafilter.extend h) :=
    Continuous.comp hg (continuous_ultrafilter_extend h)
  apply (hgh.ext_on denseRange_pure) hf
  rw [eqOn_range, Function.comp_assoc, ultrafilter_extend_extends]
  ext x; simp only [Function.comp_apply, h]
  exact Function.surjInv_eq hsurj ((f ∘ pure) x)

/-- The involution swapping the even numbers with their odd successor and vice versa. -/
def natSwap (n : ℕ) : ℕ := if Even n then n+1 else n-1

/-- The map `natSwapExtend : βℕ → βℕ`, the unique continuous extension of `pure ∘ natSwap`.
It is an involution without fixed points. -/
noncomputable def natSwapExtend : Ultrafilter ℕ → Ultrafilter ℕ :=
  Ultrafilter.extend (pure ∘ natSwap)

/-- `natSwapExtend` is continuous, being an extension along the Stone–Čech universal property. -/
theorem continuous_natSwapExtend : Continuous natSwapExtend := by
  apply continuous_ultrafilter_extend

/-- `natSwapExtend ∘ natSwapExtend = id`: since `natSwap` is its own inverse, the claim follows from
density of `range pure` in `βℕ`. -/
theorem natSwapExtend_involutive : Function.Involutive natSwapExtend := by
  have : Continuous (natSwapExtend ∘ natSwapExtend) := by refine Continuous.comp ?_ ?_ <;> exact continuous_natSwapExtend
  have eq : EqOn (natSwapExtend ∘ natSwapExtend) id (range pure) := by
    rw [eqOn_range]
    funext n
    simp [natSwapExtend, natSwap]
    grind
  exact congr_fun ((this.ext_on denseRange_pure) continuous_id eq)

/-- `pure ∘ natSwap` has dense range, since it has the same range as `pure`. -/
theorem denseRange_pure_comp_natSwap : DenseRange (pure ∘ natSwap : _ → Ultrafilter _) := by
  refine denseRange_iff_closure_range.mpr ?_
  have : range (pure ∘ natSwap : _ → Ultrafilter _) = range pure := by
    ext x
    constructor <;> simpa [natSwap] using fun n h => ⟨if Even n then n+1 else n-1, by grind⟩
  rw [this]
  exact denseRange_iff_closure_range.mp denseRange_pure

/-- `natSwapExtend` is a homeomorphism: it is continuous and involutive, hence a continuous
bijection of a compact Hausdorff space. -/
theorem isHomeomorph_natSwapExtend : IsHomeomorph natSwapExtend :=
  isHomeomorph_iff_continuous_bijective.mpr ⟨continuous_natSwapExtend, natSwapExtend_involutive.bijective⟩

/-- For σ-compact `A, B ⊆ βℕ`, `A ∩ closure B = closure A ∩ B = ∅` implies that `closure A` and
`closure B` are disjoint.

The proof separates each compact piece `Bₙ` from `closure A` (and each `Aₙ` from
`closure B`) and constructs disjoint supersets of `closure A` and `closure B`. -/
theorem IsSigmaCompact.disjoint_closure_closure {X : Type*} {A B : Set (Ultrafilter X)} (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) (hcA : Disjoint A (closure B)) (hcB : Disjoint B (closure A))
    : Disjoint (closure A) (closure B) := by
  have ⟨Aₙ, hAₙ, hAu⟩ := hA
  have ⟨Bₙ, hBₙ, hBu⟩ := hB
  have ⟨V, W, hVW⟩ : ∃ V W : ℕ → Set (Ultrafilter X), ∀n, IsOpen (V n) ∧ IsOpen (W n) ∧ Disjoint (V n) (W n) ∧ Bₙ n ⊆ W n ∧ closure A ⊆ V n := by
    have sep (n) := normal_separation (IsCompact.isClosed (hBₙ n)) (isClosed_closure (s := A)) (disjoint_iUnion_left.mp (hBu ▸ hcB) n)
    choose v w h using sep
    refine ⟨w,v,fun n => by simp [h, disjoint_comm]⟩
  have ⟨T, U, hTU⟩ : ∃ T U : ℕ → Set (Ultrafilter X), ∀n, IsOpen (T n) ∧ IsOpen (U n) ∧ Disjoint (T n) (U n) ∧ Aₙ n ⊆ T n ∧ closure B ⊆ U n := by
    have sep := fun n ↦ normal_separation (IsCompact.isClosed (hAₙ n)) (isClosed_closure (s := B)) (disjoint_iUnion_left.mp (hAu ▸ hcA) n)
    choose t u h using sep
    refine ⟨t,u,fun n => by simp [h]⟩
  let G n := (T n) ∩ ⋂ k ≤ n, (V k)
  let H n := (W n) ∩ ⋂ k ≤ n, (U k)
  let C := ⋃ n, G n
  let D := ⋃ n, H n
  have hC : IsOpen C := by
    refine isOpen_iUnion ?_
    intro n
    refine IsOpen.inter ?_ ?_
    · exact (hTU n).1
    refine Finite.isOpen_biInter ?_ ?_
    · simpa [Iic] using finite_Iic n
    intro k hk
    grind
  have hD : IsOpen D := by
    refine isOpen_iUnion ?_
    intro n
    refine IsOpen.inter ?_ ?_
    · exact (hVW n).2.1
    refine Finite.isOpen_biInter ?_ ?_
    · simpa [Iic] using finite_Iic n
    intro k hk
    grind
  have hCD : Disjoint C D := by
    simp only [disjoint_iUnion_right, disjoint_iUnion_left, C, D]
    have hGV (n k : ℕ) (h : k ≤ n) : G n ⊆ V k := by
      apply inf_le_of_right_le; apply iInf₂_le; exact h
    have hHW (n : ℕ) : H n ⊆ W n := by grind
    have hHU (n k : ℕ) (h : k ≤ n) : H n ⊆ U k := by
      apply inf_le_of_right_le; apply iInf₂_le; exact h
    have hGT (n : ℕ) : G n ⊆ T n := by grind
    intro i j
    grind [hGV i j, hHW i, hHU j i]
  have hAC : A ⊆ C := by
    rw [← hAu]
    apply iUnion_subset; intro n
    apply subset_iUnion_of_subset n
    simp only [subset_inter_iff, subset_iInter_iff, G]
    refine ⟨(hTU n).2.2.2.1, ?_⟩
    intro i hi
    apply (subset_iUnion_of_subset n (subset_rfl : Aₙ n ⊆ _)).trans
    apply subset_closure.trans
    exact hAu ▸ (hVW i).2.2.2.2
  have hBD : B ⊆ D := by
    rw [← hBu]
    apply iUnion_subset; intro n
    apply subset_iUnion_of_subset n
    simp only [subset_inter_iff, subset_iInter_iff, H]
    refine ⟨(hVW n).2.2.2.1, ?_⟩
    intro i hi
    apply (subset_iUnion_of_subset n (subset_rfl : Bₙ n ⊆ _)).trans
    apply subset_closure.trans
    exact hBu ▸ (hTU i).2.2.2.2
  have hCclD : Disjoint C (closure D) := by
    exact Disjoint.closure_right hCD hC
  have hclD := (CompactT2.Projective.extremallyDisconnected Ultrafilter.projective).open_closure D hD
  apply disjoint_of_subset _ _ (Disjoint.closure_left hCclD hclD)
  · exact closure_mono hAC
  · exact closure_mono hBD

/-- A subset of a discrete set is disjoint from the closure of the rest of that set. -/
theorem IsDiscrete.disjoint_closure_sdiff {α : Type} [TopologicalSpace α] {s t : Set α} (hs : IsDiscrete s) (ht : t ⊆ s) :
    Disjoint t (closure (s \ t)) := by
  apply disjoint_left.mpr
  intro a ha
  have ⟨u, hu, hi⟩ := isDiscrete_iff_forall_exists_isOpen.mp hs a (ht ha)
  have : u ∩ (s \ t) = ∅ := by
    rw [inter_comm, sdiff_inter_right_comm, inter_comm, hi]
    grind
  have ha : a ∈ u := And.left <| (mem_inter_iff a _ _).mp (hi ▸ mem_singleton a)
  have := Disjoint.closure_right (disjoint_iff_inter_eq_empty.mpr this) hu
  exact disjoint_left.mp this ha

/-- Every countable set is σ-compact, being a countable union of singletons. -/
theorem Set.Countable.isSigmaCompact {X : Type*} {s : Set X} [TopologicalSpace X] (hs : s.Countable) : IsSigmaCompact s := by
  have : Countable s := hs.to_subtype
  rw [← iUnion_of_singleton_coe s]
  exact isSigmaCompact_iUnion_of_isCompact _ fun _ ↦ isCompact_singleton

/-- `βℕ` splits into a set `s` and its image `natSwapExtend '' s`: take `s = closure (pure '' Even)`.
This is the key step towards `natSwapExtend` having no fixed points. -/
theorem exists_natSwapExtend_partition : ∃ s, Disjoint s (natSwapExtend '' s) ∧ natSwapExtend '' s ∪ s = Set.univ := by
  use closure (pure '' Even)
  have h₁ : Set.univ = closure ((pure ∘ natSwap : _ → Ultrafilter _) '' univ) := by
    rw [image_univ]
    refine (DenseRange.closure_range ?_).symm
    exact denseRange_pure_comp_natSwap
  have h₂ : Set.univ = natSwap '' Even ∪ Even := by
    dsimp only [natSwap]
    refine Eq.symm (eq_univ_iff_forall.mpr ?_)
    intro n
    rcases Classical.em (Even n) with he | hne
    · exact Or.inr he
    · apply Or.inl
      use n - 1
      have ho := Nat.not_even_iff_odd.mp hne
      have hns : Even (n - 1) := by grind
      constructor
      · exact (Nat.even_sub' (by grind)).mpr (by grind)
      simp [natSwap, hns]
      grind
  have hcl {s} : natSwapExtend '' closure s = closure (natSwapExtend '' s) := by
    rw [Set.image, Set.image]
    repeat conv in natSwapExtend _ = _ =>
      rw [← isHomeomorph_natSwapExtend.homeomorph_apply]
    rw [← Set.image, ← Set.image, isHomeomorph_natSwapExtend.homeomorph.image_closure]
  have hpp {s} : natSwapExtend '' pure '' s = pure '' natSwap '' s := by
    simp [natSwap, natSwapExtend, ← image_comp]
  rw [hcl, ← closure_union, hpp, ← image_union, ← h₂, image_univ]
  refine ⟨?_, denseRange_pure.closure_range⟩
  have : (pure : ℕ → Ultrafilter ℕ) '' natSwap '' Even = (range pure) \ pure '' Even := by
    rw [range_diff_image Ultrafilter.pure_injective]
    apply image_eq_image Ultrafilter.pure_injective |>.mpr
    simp only [image, natSwap, compl_def, Set.ext_iff, mem_setOf_eq]
    intro x
    constructor
    · intro ⟨n, hn, h⟩
      rw [if_pos] at h
      · apply Nat.not_even_iff.mpr
        rw [← h, Nat.add_mod, Nat.even_iff.mp hn]
      exact hn
    · intro h
      use x - 1
      have ho : Odd x := Nat.not_even_iff_odd.mp h
      constructor
      · exact (Nat.even_sub' (by grind)).mpr (by grind)
      rw [if_pos]
      · grind
      · refine Odd.tsub_odd ho ?_
        exact Nat.odd_iff.mpr rfl
  apply IsSigmaCompact.disjoint_closure_closure
  · apply Countable.isSigmaCompact
    exact Countable.image (to_countable Even) pure
  · apply Countable.isSigmaCompact
    exact Countable.image (to_countable (natSwap '' Even)) pure
  · rw [this]
    apply IsDiscrete.disjoint_closure_sdiff
    · exact IsInducing.isDiscrete_range isDenseInducing_pure.isInducing
    simp
  · have : (pure : ℕ → Ultrafilter ℕ) '' Even = (range pure) \ pure '' natSwap '' Even := by
      simp [this]
    rw [this]
    apply IsDiscrete.disjoint_closure_sdiff
    · exact IsInducing.isDiscrete_range isDenseInducing_pure.isInducing
    simp

/-- `natSwapExtend` has no fixed points. -/
theorem ne_natSwapExtend (F : Ultrafilter ℕ) : F ≠ natSwapExtend F := by
  have ⟨s, hds, hu⟩ := exists_natSwapExtend_partition
  rcases Classical.em (F ∈ s) with h | h
  · grind
  · have : F ∈ natSwapExtend '' s := by
      exact ((mem_union _ _ _).mp (hu ▸ mem_univ F)).resolve_right h
    have := mem_image_of_mem natSwapExtend this
    rw [← image_comp, Function.Involutive.comp_self natSwapExtend_involutive] at this
    grind

/-- For a countably infinite discrete `S ⊆ βℕ`, the closure of `S` is homeomorphic to `βℕ`.

The homeomorphism is the extension `f̂` of a bijection `f : ℕ ≃ S`. -/
noncomputable def Index.homeomorphClosure (S : Index) (h : IsDiscrete S.val) : Ultrafilter ℕ ≃ₜ closure S.val := by
  letI : TopologicalSpace ℕ := ⊥
  let E : ℕ ≃ S :=
    nonempty_equiv_of_countable.some
  let f a := (E a).val
  let f' := Ultrafilter.extend f
  have hf' : Continuous f' := by
    apply continuous_ultrafilter_extend
  have hff (A) : f '' A = f' '' pure '' A := by simp [f', ← image_comp]
  have ultra (U : Ultrafilter ℕ) (A : Set ℕ) (h : A ∈ U) : (f' U) ∈ closure (f '' A) := by
    rw [hff A]
    apply mem_closure_image (Continuous.continuousAt hf')
    apply mem_closure_of_tendsto (Ultrafilter.tendsto_pure_self U)
    have : A = { x | (pure : ℕ → Ultrafilter ℕ) x ∈ pure '' A} := by
      rw [← setOf_mem_eq (s := A)]
      apply setOf_inj.mpr
      funext n
      exact (Function.Injective.mem_set_image Ultrafilter.pure_injective).symm.eq
    rw [Filter.eventually_iff, ← this]
    exact h
  have inj : Function.Injective f' := by
    intro F G
    apply (@not_imp_not (F = G) _).mp
    intro hne
    have ⟨s, hF, hG⟩ : ∃ s, s ∈ F ∧ sᶜ ∈ G := Ultrafilter.exists_mem_compl_mem_of_ne hne
    have hs : (f '' s).Countable := Countable.image (to_countable s) f
    have hsc : (f '' sᶜ).Countable := Countable.image (to_countable sᶜ) f
    have (t : Set ℕ) : f '' tᶜ = S.val \ (f '' t) := by
      have : S.val = f '' t ∪ f '' tᶜ := by
        ext F
        simp only [image_union_image_compl_eq_range, mem_range, f]
        exact ⟨fun h => ⟨E.symm ⟨F, h⟩, by simp⟩, fun ⟨n, hn⟩ => by simp [← hn]⟩
      rw [this, image_union_image_compl_eq_range, range_diff_image]
      intro n m h
      simpa [f] using congr_arg E.symm (Subtype.ext h)
    have hdis : Disjoint (closure (f '' s)) (closure (f '' sᶜ)) := by
      apply IsSigmaCompact.disjoint_closure_closure (hs.isSigmaCompact) (hsc.isSigmaCompact)
      · rw [this]
        apply IsDiscrete.disjoint_closure_sdiff h
        grind
      · rw [← compl_compl s, this sᶜ, compl_compl]
        apply IsDiscrete.disjoint_closure_sdiff h
        grind
    apply ne_of_mem_of_not_mem (ultra F _ hF)
    exact hdis.notMem_of_mem_right (ultra G _ hG)
  have r : range f' = closure (range f) := by
    refine Subset.antisymm ?_ ?_
    · intro U hU
      have ⟨U', hU'⟩ := mem_range.mp hU
      rw [← hU']
      have := (Ultrafilter.mem_or_compl_mem U' univ).resolve_right (by simp)
      simpa using ultra U' _ this
    · refine (isCompact_range hf').isClosed.closure_subset_iff.mpr ?_
      refine range_subset_range_iff_exists_comp.mpr ⟨pure, ?_⟩
      rw [ultrafilter_extend_extends]
  have : closure (range f) = closure S.val := by
    refine congr_arg _ (ext ?_)
    intro U
    constructor <;> intro h
    · have ⟨a, ha⟩ := h; simp [← ha, f]
    · exact ⟨E.symm ⟨U, by simp [h]⟩, by simp [f]⟩
  apply Homeomorph.trans _ (Homeomorph.setCongr this)
  apply Homeomorph.trans _ (Homeomorph.setCongr r)
  have : Continuous (Equiv.ofInjective f' inj) := by
    have : ⇑(Equiv.ofInjective f' inj) = fun x => ⟨f' x, mem_range_self x⟩ := by congr
    rw [this]
    exact Continuous.subtype_mk hf' mem_range_self
  exact Continuous.homeoOfEquivCompactToT2 this

/-- Every countably infinite `S ⊆ βℕ` contains a countably infinite discrete subset,
since `βℕ` is Hausdorff. -/
theorem Index.exists_isDiscrete_subset (S : Index) : ∃ T : Index, IsDiscrete T.val ∧ T.val ⊆ S.val := by
  have ⟨t, hi, hd⟩ : ∃ t : Set S.val, t.Infinite ∧ IsDiscrete t := by
    conv in IsDiscrete _ => rw [isDiscrete_iff_discreteTopology]
    apply exists_infinite_discreteTopology
  refine ⟨⟨t, ?_, ?_⟩, ?_, ?_⟩
  · exact Infinite.image injOn_subtype_val hi
  · exact Countable.image (to_countable t) Subtype.val
  · exact IsDiscrete.image hd IsInducing.subtypeVal
  · grind

/-- For every countably infinite `S ⊆ βℕ` the closure of `S` has cardinality `2 ^ 𝔠`,
i.e. the same cardinality as `βℕ` itself. -/
theorem Index.mk_ultrafilter_eq_mk_closure (S : Index) : #(Ultrafilter ℕ) = #(closure S.val) := by
  have ⟨T, hT, hST⟩ := Index.exists_isDiscrete_subset S
  apply eq_of_le_of_ge
  · rw [(Index.homeomorphClosure T hT).toEquiv.cardinal_eq]
    exact mk_le_mk_of_subset (closure_mono hST)
  · exact mk_set_le (closure S.val)

/-- The index family transported to a well-ordered type of the same cardinality,
so that the recursion `pick` can run over its initial segments. -/
abbrev IndexOrd := (#Index).ord.ToType

/-- The chosen bijection between `IndexOrd` and `Index`. -/
noncomputable
def indexOrdEquiv : IndexOrd ≃ Index :=
  (Cardinal.eq.mp (mk_ord_toType #Index)).some

/-- The recursion step: if `Q` is small (`#Q < #βℕ`), then `closure S \ (S ∪ natSwapExtend '' Q)` is
nonempty, because `#(closure S) = 2 ^ 𝔠` dominates `ℵ₀ + #Q`. -/
theorem Index.closure_sdiff_nonempty {Q : Set (Ultrafilter ℕ)} (S : Index) (h : #Q < #(Ultrafilter ℕ)) : (closure S.val \ (S.val ∪ natSwapExtend '' Q)).Nonempty := by
  refine diff_nonempty_of_mk_lt_mk ?_
  rw [← Index.mk_ultrafilter_eq_mk_closure]
  apply lt_of_le_of_lt (mk_union_le S.val (natSwapExtend '' Q))
  rw [mk_eq_aleph0, mk_image_eq natSwapExtend_involutive.injective]
  rcases le_or_gt #Q ℵ₀ with haleph | haleph
  · rw [add_eq_left (by rfl) haleph]
    exact lt_trans (cantor _) (lt_of_lt_of_eq (cantor _) mk_ultrafilter_nat.symm)
  rw [add_eq_right (le_of_lt haleph) (le_of_lt haleph)]
  exact h

/-- The transfinite recursion `p`: at stage `𝔨` with countably infinite set `S_𝔨` choose a point of
`closure S_𝔨 \ (S_𝔨 ∪ G '' {p 𝔪 | 𝔪 < 𝔨})`, which is possible by
`Index.closure_sdiff_nonempty`. -/
noncomputable
def pick : IndexOrd → Ultrafilter ℕ :=
  IsWellFounded.fix LT.lt fun 𝔨 ih =>
    let f (𝔞 : Iio 𝔨) := ih 𝔞 𝔞.prop
    let Q := range f
    have h : #Q < #(Ultrafilter ℕ) := by
      rw [← mk_index]
      apply lt_of_le_of_lt _ <| (mk_ord_toType #Index) ▸ mk_Iio_lt 𝔨 (by simp)
      simp_rw [Q]
      exact mk_range_le
    (Index.closure_sdiff_nonempty (indexOrdEquiv 𝔨) h).some

/-- The Novák space `X = β(ℕ) ∪ Q`, where `Q = range pick`. It is countably compact while
`X × X` is not. -/
abbrev novakSpace : Set (Ultrafilter ℕ) := (range pick) ∪ (range pure)

/-- The copy of `ℕ` inside the Novák space. -/
abbrev novakPure (n : ℕ) : novakSpace := ⟨pure n, by simp⟩

/-- Points in the range of `novakPure` are principal ultrafilters. -/
theorem exists_eq_pure_of_mem_range_novakPure {x : novakSpace} (h : x ∈ range novakPure) : ∃ n, x.val = pure n := by
  simp_all only [novakSpace, mem_range]
  refine ⟨h.choose, by grind⟩

/-- A point chosen from `s \ t` differs from every point of `t`. -/
theorem Set.Nonempty.choose_ne_of_mem {α : Type*} {s t : Set α} {x : α} {hs : (s \ t).Nonempty} (h : x ∈ t) : hs.choose ≠ x := by
  grind

/-- Later choices avoid the `natSwapExtend`-images of earlier ones, by construction of `pick`. -/
theorem pick_ne_natSwapExtend_pick {𝔨 𝔫 : IndexOrd} (h : 𝔫 < 𝔨) : pick 𝔨 ≠ natSwapExtend (pick 𝔫) := by
  rw [pick, IsWellFounded.fix_eq]
  apply Set.Nonempty.choose_ne_of_mem
  simp only [mem_union, mem_image, mem_range, Subtype.exists, mem_Iio, exists_prop,
    exists_exists_and_eq_and]
  exact Or.inr ⟨𝔫, h, by simp⟩

/-- `Q` and `natSwapExtend '' Q` are disjoint: the three cases of trichotomy are handled by
`pick_ne_natSwapExtend_pick`, `ne_natSwapExtend` and involutivity of `natSwapExtend`. -/
theorem disjoint_range_pick_image_natSwapExtend : Disjoint (range pick) (natSwapExtend '' range pick) := by
  refine disjoint_right.mpr ?_
  simp_all only [mem_image, mem_range, exists_exists_eq_and, not_exists, forall_exists_index,
    forall_apply_eq_imp_iff]
  by_contra! ⟨𝔫, 𝔨, h⟩
  rcases lt_trichotomy 𝔫 𝔨 with hlt | heq | hgt
  · exact pick_ne_natSwapExtend_pick hlt h
  · exact ne_natSwapExtend (pick 𝔫) (heq ▸ h)
  · exact pick_ne_natSwapExtend_pick hgt (natSwapExtend_involutive (pick 𝔫) ▸ congr_arg natSwapExtend h.symm)

/-- A space is countably compact if for every countably infinite subset
there is an accumulation point in the space. -/
theorem isCountablyCompact_of_exists_mem_closure_sdiff {X : Set (Ultrafilter α)} (h : ∀ B ⊆ X, B.Infinite → B.Countable → ∃ x ∈ X, x ∈ closure B \ B) : IsCountablyCompact X := by
  apply isCountablyCompact_iff_infinite_subset_has_accPt.mpr
  intro B hB hinf
  have ⟨B', hB', hinf, hcount⟩ : ∃ B' ⊆ B, B'.Countable ∧ B'.Infinite := by
    exact Infinite.exists_subset_countable_infinite hinf
  have ⟨x, hx, hpt⟩ := h B' (hB'.trans hB) hcount hinf
  refine ⟨x, hx, ?_⟩
  apply AccPt.mono _ (Filter.principal_mono.mpr hB')
  apply (clusterPt_principal.mp _).resolve_left
  · simpa using And.right hpt
  refine mem_closure_iff_clusterPt.mp ?_
  simpa using And.left hpt

/-- The Novák space is countably compact.

As for all countably infinite `B ⊆ X` we choose a accumulation point of `B` using `pick` and add it
to `novakSpace`. -/
instance : CountablyCompactSpace (novakSpace : Set (Ultrafilter ℕ)) := by
  refine isCountablyCompact_iff_countablyCompactSpace.mp ?_
  apply isCountablyCompact_of_exists_mem_closure_sdiff
  intro B hB hinf hcount
  let S : Index := ⟨B, hinf, hcount⟩
  let 𝔩 := (indexOrdEquiv.symm S)
  use pick 𝔩
  constructor
  · simp
  simp only [pick, mem_diff]
  rw [IsWellFounded.fix_eq]
  constructor
  · apply mem_of_subset_of_mem _ (Set.Nonempty.some_mem _)
    simp [𝔩, S]
  · apply disjoint_left.mp _ (Set.Nonempty.some_mem _)
    apply disjoint_of_subset_right _ disjoint_sdiff_left
    simp [𝔩, S]

/-- The graph of `natSwapExtend` restricted to the Novák space; the counterexample set
for the countable compactness of `novakSpace × novakSpace`. -/
abbrev swapGraph : Set (novakSpace × novakSpace) := { ⟨x, y⟩ | y = natSwapExtend x }

/-- The graph of `natSwapExtend` is closed, `natSwapExtend` being continuous into a Hausdorff space. -/
theorem isClosed_swapGraph : IsClosed swapGraph := by
  refine isClosed_eq ?_ ?_
  · exact Continuous.snd' continuous_subtype_val
  refine Continuous.comp' ?_ ?_
  · exact continuous_natSwapExtend
  · exact Continuous.fst' continuous_subtype_val

/-- The graph of `natSwapExtend` is infinite as it contains `(pure n, natSwapExtend (pure n))` for
every `n`. -/
theorem infinite_swapGraph : swapGraph.Infinite := by
  simp only [swapGraph]
  let f (n : ℕ) : swapGraph := ⟨⟨⟨pure n, by simp [novakSpace]⟩, ⟨natSwapExtend (pure n), by {simp [novakSpace]; exact Or.inr ⟨if Even n then n + 1 else n - 1, by simp [natSwapExtend, natSwap]⟩}⟩⟩, by simp⟩
  have hf : Function.Injective f := by
    intro n m h
    simp [f] at h
    exact Ultrafilter.pure_injective h.left
  refine infinite_coe_iff.mp (infinite_univ_iff.mp ?_)
  apply infinite_of_injOn_mapsTo (injOn_univ.mpr hf) (Set.mapsTo_univ f Set.univ)
  exact infinite_univ

/-- No accumulation point of a discrete set `s` resides in `s`. -/
theorem IsDiscrete.notMem_of_accPt {s : Set α} [TopologicalSpace α] (h : IsDiscrete s) {a : α} (ha : AccPt a (Filter.principal s)) : a ∉ s := by
  intro has
  have ⟨o, ho, hio⟩ := isDiscrete_iff_forall_exists_isOpen.mp h a has
  have hao : a ∈ o := by
    have : a ∈ o ∩ s := by grind only [= mem_singleton_iff]
    simp [mem_inter_iff] at this
    exact this.left
  have ⟨b, hb⟩ := accPt_iff_nhds.mp ha o (mem_nhds_iff.mpr ⟨o, by simp [ho, hao]⟩)
  grind only [= mem_singleton_iff]

/-- An accumulation point of a equality of two functions `f` and `g` projects to an accumulation
point of the domain of `f` if `g` is injective. -/
theorem AccPt.fst_of_mem_graph {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {p : α × β} {f : α → γ} {g : β → γ} (hm : p ∈ { ⟨a,b⟩ : α × β | g b = f a }) (hi : Function.Injective g) (h : AccPt p (Filter.principal { ⟨a,b⟩ | g b = f a })) : AccPt p.1 (Filter.principal (Prod.fst '' { ⟨a,b⟩ : α × β | g b = f a })) := by
  refine accPt_principal_iff_clusterPt.mpr ?_
  have h' := accPt_principal_iff_clusterPt.mp h
  apply h'.map continuousAt_fst
  refine Filter.tendsto_principal_principal.mpr ?_
  grind

/-- The only points that are both in the graph of `natSwapExtended` and in `novakSpace × novakSpace`
are those that are principal filters in their first coordinate. -/
theorem range_novakPure_eq_fst_image_swapGraph : range novakPure = Prod.fst '' swapGraph := by
  ext F
  simp only [mem_range, mem_image, mem_setOf_eq, Prod.exists, exists_and_right, Subtype.exists,
    mem_union, exists_prop, exists_eq_right]
  constructor
  · intro ⟨n,h⟩
    refine Or.inr ⟨natSwap n, by simp [← h, natSwapExtend]⟩
  · intro h
    rcases h with h | ⟨n, h⟩
    · have : natSwapExtend F ∈ range pick := by grind
      rcases F.prop with hF | hF
      · exact disjoint_range_pick_image_natSwapExtend.notMem_of_mem_left this (mem_image_of_mem natSwapExtend hF) |>.elim
      grind
    refine ⟨natSwap n, Subtype.ext ?_⟩
    have := natSwapExtend_involutive F ▸ congr_arg natSwapExtend h
    simp [← this, natSwapExtend]

/-- The square of the Novák space is not countably compact: the infinite set
`swapGraph` has no accumulation point `novakSpace × novakSpace`. -/
theorem not_countablyCompactSpace_prod : ¬CountablyCompactSpace (novakSpace × novakSpace) := by
  intro h
  have ⟨p, _, hp⟩ := h.isCountablyCompact_univ.exists_accPt_of_infinite (subset_univ _) infinite_swapGraph
  have hpm := isClosed_iff_accPt.mp isClosed_swapGraph p hp
  have hp1 := AccPt.fst_of_mem_graph (f := fun (x : novakSpace) => natSwapExtend ↑x) hpm Subtype.val_injective hp
  rw [← range_novakPure_eq_fst_image_swapGraph] at hp1
  have : IsDiscrete (range novakPure) := by
    apply IsInducing.isDiscrete_range (IsInducing.subtypeVal.of_comp_iff.mp ?_)
    simpa [Function.comp_def] using isDenseInducing_pure.isInducing
  apply IsDiscrete.notMem_of_accPt this hp1
  exact (range_eq_iff _ _).mp range_novakPure_eq_fst_image_swapGraph |>.right p.1 (mem_image_of_mem Prod.fst hpm)
