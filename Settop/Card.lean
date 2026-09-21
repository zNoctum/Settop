import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Compactness.CountablyCompact
import Mathlib.Data.Countable.Defs
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Prod
import Mathlib.Data.Finset.Image
import Mathlib.SetTheory.Cardinal.Regular

open Cardinal Filter Set

variable (X : Type*)

/-- The index family `𝓕` of the Novák construction: the countably infinite subsets of `βℕ`.
Every such set is used exactly once as a stage of the transfinite recursion `pick`. -/
abbrev Index := { s : Set (Ultrafilter ℕ) // s.Infinite ∧ s.Countable }

instance {S : Index} : Infinite S.val := Infinite.to_subtype S.prop.1

instance {S : Index} : Countable S.val := Countable.to_subtype S.prop.2

/-- `Ultrafilter ℕ` is infinite, as `pure` embeds `ℕ` into it. -/
instance : Infinite (Ultrafilter ℕ) := Infinite.of_injective pure Ultrafilter.pure_injective

/-- Two unequal ultrafilters on a type `α` are differentiated by atleast one `s : Set α` -/
theorem Ultrafilter.exists_mem_compl_mem_of_ne {α : Type*} {F G : Ultrafilter α} (h : F ≠ G) :
    ∃ s, s ∈ F ∧ sᶜ ∈ G := by
  rw [Ne.eq_def, Ultrafilter.ext_iff] at h
  push Not at h
  have ⟨s, hs⟩ := h
  rcases hs with h' | h'
  · exact ⟨s, h'.left, Ultrafilter.compl_mem_iff_notMem.mpr h'.right⟩
  · exact ⟨sᶜ, Ultrafilter.compl_mem_iff_notMem.mpr h'.left, (compl_compl s).symm ▸ h'.right⟩

/-- The carrier `S = { (n, f) | n : ℕ, f : 𝒫 {0, …, n} → 𝒫 {0, …, n} }` of the independent family.

It is countably infinite, so an independent family of subsets of `Count` transfers to one of
subsets of `ℕ` along `countEquiv`. -/
def Count := Σ n : ℕ, Set (Iic n) → Set (Iic n)

/-- `Count` is countable: it is a countable union of the finite function spaces
`Set (Iic n) → Set (Iic n)`, so `#Count = ∑ n, (2 ^ n) ^ 2 ^ n = ℵ₀`. -/
instance : Countable Count := by
  refine mk_le_aleph0_iff.mp ?_
  simp [Count, mk_eq_aleph0, Std.le_refl]

/-- `Count` is infinite, as `(n, id)` belongs to it for every `n : ℕ`. -/
instance : Infinite Count := by
  apply Infinite.of_injective (fun n => ⟨n,id⟩)
  intro n m h
  grind

/-- The chosen bijection between `ℕ` and `Count`, which exists as both are countably infinite. -/
noncomputable
def countEquiv : ℕ ≃ Count := by
  have : #ℕ = #Count := (mk_eq_aleph0 ℕ).trans (mk_eq_aleph0 Count).symm
  exact (Cardinal.eq.mp this).some

/-- A well-ordered type of the same cardinality as `Set ℕ`, used to enumerate the members of the
independent family. -/
abbrev PNOrd := (#(Set ℕ)).ord.ToType

/-- The chosen bijection between `PNOrd` and `Set ℕ`. -/
noncomputable
def pnOrdEquiv : PNOrd ≃ Set ℕ :=
  (Cardinal.eq.mp (mk_ord_toType #(Set ℕ))).some

/-- `PNOrd` is infinite, being equipotent to `Set ℕ`. -/
instance : Infinite PNOrd := pnOrdEquiv.infinite_iff.mpr Infinite.set

/-- The restriction `s ∩ Iic n` of `s : Set ℕ` to the initial segment `Iic n`. -/
def restrictIic {n : ℕ} (s : Set ℕ) : Set (Iic n) :=
  fun n ↦ ↑n ∈ s

/-- Distinct subsets of `ℕ` differ on some initial segment: taking `m` in the symmetric difference
of `s` and `t` already separates `s ∩ {0, …, m}` from `t ∩ {0, …, m}`. -/
theorem exists_restrictIic_ne {s t : Set ℕ} (h : s ≠ t) :
    ∃ m, (restrictIic s : Set (Iic m)) ≠ restrictIic t := by
  have ⟨x, hx⟩ : ∃ x, (x ∈ s ∧ x ∉ t) ∨ (x ∈ t ∧ x ∉ s) := by
    have := symmDiff_nonempty.mpr h
    exact ⟨this.choose, mem_symmDiff.mp this.choose_spec⟩
  refine ⟨x, Function.ne_iff.mpr ⟨⟨x, by simp⟩, ?_⟩⟩
  simp only [restrictIic]
  grind

/-- Distinct subsets of `ℕ` differ on *every* sufficiently long initial segment: once a separating
point lies below `n`, all larger `n` separate them as well. -/
theorem exists_forall_restrictIic_ne {s t : Set ℕ} (h : s ≠ t) :
    ∃ m, ∀ n ≥ m, (restrictIic s : Set (Iic n)) ≠ restrictIic t := by
  convert exists_restrictIic_ne h with m
  constructor
  · grind
  intro h n hn
  apply Function.ne_iff.mpr
  have ⟨k, hk⟩ := Function.ne_iff.mp h
  use ⟨k, by grind⟩
  simp_all [restrictIic]

/-- Family of systems of sets used to create ultrafilters from `Set (Set ℕ)`.
-/
def countFam (σ δ : PNOrd) : Set Count :=
  { ⟨_, f⟩ : Count | f (restrictIic (pnOrdEquiv σ)) = restrictIic (pnOrdEquiv δ)}

/-- Two members of the family sharing their first index meet in a finite set. -/
theorem finite_countFam_inter (σ : PNOrd) {δ τ : PNOrd} (h : δ ≠ τ) :
    (countFam σ δ ∩ countFam σ τ).Finite := by
  let A := {⟨n, f⟩ : Count |
    (restrictIic (pnOrdEquiv δ) : Set (Iic n)) = restrictIic (pnOrdEquiv τ) ∧
      f (restrictIic (pnOrdEquiv σ)) = restrictIic (pnOrdEquiv δ) }
  let B := {⟨n, f⟩ : Count |
    (restrictIic (pnOrdEquiv δ) : Set (Iic n)) = restrictIic (pnOrdEquiv τ) }
  have ⟨m, hm⟩ := exists_forall_restrictIic_ne (pnOrdEquiv.injective.ne h)
  let C := {⟨n, f⟩ : Count | n < m}
  convert_to A.Finite
  · simp only [A, countFam]
    ext ⟨n, f⟩
    grind
  suffices B.Finite by
    exact Finite.sep this fun c ↦ c.snd (restrictIic (pnOrdEquiv σ)) = restrictIic (pnOrdEquiv δ)
  have : B ⊆ C := by grind
  apply Set.Finite.subset _ this
  have e : C ≃ Σ n : Iio m, Set (Iic n.val) → Set (Iic n.val) := by
    refine Equiv.ofBijective (fun (⟨⟨n, f⟩, h⟩ : C) => ⟨⟨n, by simp_all [C]⟩,f⟩) ?_
    refine Function.bijective_iff_has_inverse.mpr ⟨(fun (⟨⟨n,h⟩,f⟩) => ⟨⟨n,f⟩, by
      simp_all only [ne_eq, ge_iff_le, mem_setOf_eq, C]; trivial⟩), ?_⟩
    grind
  have : ∀ c ∈ B, c.fst < m := by grind
  apply (Equiv.finite_iff e).mpr
  exact Finite.instSigma

/-- Any finite choice from the family has countably infinite intersection. -/
theorem mk_iInter_countFam {F : Finset PNOrd} (g : F → PNOrd) :
    #(⋂ σ, ⋂ h : σ ∈ F, countFam σ (g ⟨σ,h⟩)) = ℵ₀ := by
  let s := (⋂ σ, ⋂ h : σ ∈ F, countFam σ (g ⟨σ, h⟩))
  suffices Infinite s by
    apply mk_eq_aleph0 ↑(⋂ σ, ⋂ (h : σ ∈ F), countFam σ (g ⟨σ, h⟩))
  suffices ∃ m, ∀ n ≥ m, ∃ f, ⟨n, f⟩ ∈ s by
    have ⟨m, hm⟩ := this
    choose fₙ hfₙ using hm
    let f (n : ℕ) : s := ⟨⟨n + m, fₙ (n + m) (Nat.le_add_left m n)⟩, ?_⟩
    · apply Infinite.of_injective f
      intro k l h
      simp_all only [ge_iff_le, Subtype.mk.injEq, f]
      simpa using congr_arg Sigma.fst h
    exact mem_preimage.mp (hfₙ (n + m) (Nat.le_add_left m n))
  have : ∀ o ∈ F.offDiag, ∀ᶠ (n : ℕ) in atTop,
      (restrictIic (pnOrdEquiv o.1) : Set (Iic n)) ≠ restrictIic (pnOrdEquiv o.2) := by
    intro ⟨σ, τ⟩
    simp_all only [Finset.mem_offDiag, ne_eq, eventually_atTop, ge_iff_le, and_imp]
    by_contra! ⟨hσ, hτ, hne, h⟩
    have : pnOrdEquiv σ = pnOrdEquiv τ := by
      ext n
      have ⟨k, _, hk⟩ := h n
      simpa using congr_fun hk ⟨n, by simpa⟩
    exact hne <| pnOrdEquiv.injective this
  have ⟨m, hm⟩ : ∃ m, ∀ n ≥ m,
      Function.Injective fun (σ : F) => (restrictIic (pnOrdEquiv σ) : Set (Iic n)) := by
    have ⟨m, hm⟩ := eventually_atTop.mp <| Finset.eventually_all _ |>.mpr this
    refine ⟨m, fun n hn σ τ h => ?_⟩
    simp_all only [Finset.mem_offDiag, ne_eq, eventually_atTop, ge_iff_le, and_imp, Prod.forall,
      SetLike.coe_mem]
    by_contra!
    exact hm n hn σ τ (Finset.coe_mem σ) (Finset.coe_mem τ) (by simpa) h
  refine ⟨m, fun n hn => ?_⟩
  classical let f (s : Set (Iic n)) : Set (Iic n) :=
    if h : ∃! σ : F, s = (restrictIic (pnOrdEquiv σ)) then ( by
      choose σ h _ using h
      apply restrictIic (pnOrdEquiv (g ⟨σ, by simp⟩))
    ) else ∅
  use f
  simp only [countFam, mem_iInter, mem_setOf_eq, s, f]
  intro σ hσ
  have : ∃! τ : F, (restrictIic (pnOrdEquiv σ) : Set (Iic n)) = restrictIic (pnOrdEquiv τ) := by
    refine ExistsUnique.intro ⟨σ, hσ⟩ (by grind) ?_
    intro τ heq
    exact hm n hn heq |>.symm
  simp [dif_pos this]
  congr
  grind

/-- A set `S` whose finite subsets all have infinite intersection extends to a nonprincipal
ultrafilter. -/
theorem exists_hyperfilter_of_finite_inter_infinite {α : Type*} (S : Set (Set α)) (cond : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Infinite) :
    ∃ F : Ultrafilter α, S ⊆ F.sets ∧ (F : Filter α) ≤ cofinite := by
  have h : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ (S ∪ {{x}ᶜ | x : α}) → (⋂₀ (↑T : Set (Set α))).Nonempty := by
    intro T hT
    have ⟨s, t, hstT, hs, ht⟩ := Finset.subset_union_elim hT
    rw [← hstT, Finset.coe_union, sInter_union]
    have ⟨t', ht', hfint'⟩ : ∃ t' : Set α, ⋂₀ t = t'ᶜ ∧ t'.Finite := by
      use ⋃₀ {sᶜ | s ∈ t}
      constructor
      · simp [compl_sUnion, sInter_eq_biInter]
      refine Finite.sUnion ?_ ?_
      · exact finite_image_iff compl_injective.injOn |>.mpr <| Finset.finite_toSet t
      intro _ ⟨s, hs, hs'⟩
      have ⟨c, hc⟩ : ∃ c, {c}ᶜ = s := by simpa using ht.trans diff_subset <| hs
      simp [← hs', ← hc]
    rw [ht']
    have := cond s hs
    refine nonempty_coe_sort.mp <| mk_ne_zero_iff.mp <| ne_of_gt <| lt_of_lt_of_le mk_lt_aleph0
      <| infinite_iff.mp <| infinite_coe_iff.mpr <| Set.Infinite.diff ?_ ?_ <;> simpa
  choose F hF using Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty (S ∪ {{x}ᶜ | x : α}) h
  refine ⟨F, union_subset_iff.mp hF |>.left, ?_⟩
  apply Filter.le_cofinite_iff_compl_singleton_mem.mpr
  intro x
  convert setOf_subset.mp (union_subset_iff.mp hF |>.right) {x}ᶜ (by simp)

/-- `Ultrafilter ℕ` has cardinality `2 ^ 𝔠`. -/
theorem mk_ultrafilter_nat : #(Ultrafilter ℕ) = 2 ^ ((2 : Cardinal) ^ ℵ₀) := by
  apply eq_of_le_of_ge
  · have : #(Set (Set ℕ)) = 2 ^ (2 : Cardinal) ^ ℵ₀ := by simp
    refine le_of_le_of_eq ?_ this
    suffices Function.Injective (fun (F : Ultrafilter ℕ) => (· ∈ F)) by
      exact mk_le_of_injective this
    intro F G
    by_contra! ⟨hd, hne⟩
    have ⟨s, hF, hG⟩ : ∃ s, s ∈ F ∧ sᶜ ∈ G := Ultrafilter.exists_mem_compl_mem_of_ne hne
    exact congr_fun hd s
      |> Iff.of_eq
      |>.mp hF
      |> Ultrafilter.compl_mem_iff_notMem.mp hG
  have ⟨τ, γ, h⟩ := exists_pair_ne PNOrd
  have : 2 ^ (2 : Cardinal) ^ ℵ₀ = #(PNOrd → ({τ,γ} : Set PNOrd)) := by
    simp [Finset.card_pair h]
  refine le_of_eq_of_le this ?_
  have : #(Ultrafilter ℕ) = #(Ultrafilter Count) := by
    refine mk_congr ?_
    refine Equiv.ofBijective (fun F => F.map countEquiv) ?_
    refine Function.bijective_iff_has_inverse.mpr ⟨fun F => F.map countEquiv.symm, ?_⟩
    constructor <;> {
      intro _; simp
    }
  refine le_of_le_of_eq ?_ this.symm
  let M (g : PNOrd → ({τ,γ} : Set PNOrd)) : { f : Ultrafilter Count // ∀ x, f ≠ pure x} := by
    choose F hF using Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty
      ((range fun σ => countFam σ (g σ)) ∪ {{c}ᶜ | c : Count}) ?_
    refine ⟨F, fun c => ?_⟩
    by_contra! h
    have hcc : {c}ᶜ ∈ F := by
      apply hF; simp
    have hc : {c} ∈ F := by rw [h]; exact Ultrafilter.mem_pure.mpr rfl
    exact Ultrafilter.compl_notMem_iff.mpr hc hcc
  · intro T hT
    have ⟨s, t, hstT, hs, ht⟩ := Finset.subset_union_elim hT
    have := Finset.subset_set_image_iff (s := univ) |>.mp (by rwa [image_univ])
    have ⟨F, _, hF⟩ := this
    rw [← hstT, ← hF, Finset.coe_union, sInter_union]
    have ⟨t', ht', hfint'⟩ : ∃ t' : Set Count, ⋂₀ t = t'ᶜ ∧ t'.Finite := by
      use ⋃₀ {sᶜ | s ∈ t}
      constructor
      · simp [compl_sUnion, sInter_eq_biInter]
      refine Finite.sUnion ?_ ?_
      · exact finite_image_iff compl_injective.injOn |>.mpr <| Finset.finite_toSet t
      intro _ ⟨s, hs, hs'⟩
      have ⟨c, hc⟩ : ∃ c, {c}ᶜ = s := by simpa using ht.trans diff_subset <| hs
      simp [← hs', ← hc]
    rw [ht']
    have : (⋂ a ∈ F, countFam a ↑(g a)).Infinite:= by
      refine infinite_coe_iff.mp <| infinite_iff.mpr <| le_of_eq <| Eq.symm ?_
      convert mk_iInter_countFam (fun (σ : F) => g σ)
    refine nonempty_coe_sort.mp <| mk_ne_zero_iff.mp <| ne_of_gt <| lt_of_lt_of_le mk_lt_aleph0
      <| infinite_iff.mp <| infinite_coe_iff.mpr <| Set.Infinite.diff ?_ ?_ <;> simpa
  apply le_trans _ (mk_subtype_le (∀ x, · ≠ pure x))
  suffices Function.Injective M by
    exact mk_le_of_injective this
  intro f g
  contrapose
  intro h
  have ⟨σ, hσ⟩ : ∃ σ : PNOrd, (f σ).val ≠ (g σ).val := by grind
  by_contra! heq
  have (h) {σ}: (countFam σ (h σ)) ∈ (M h).val := by
    have h1 : (range fun σ ↦ countFam σ ↑(h σ)) ⊆ (M h).val.sets := by grind
    have h2 : countFam σ ↑(h σ) ∈ (range fun σ ↦ countFam σ ↑(h σ)) := by grind
    exact Filter.mem_sets.mp (h1 h2)
  have : (countFam σ (f σ)) ∩ (countFam σ (g σ)) ∈ (M f).val :=
    inter_mem (this f) (heq ▸ this g) |> Ultrafilter.mem_coe.mp
  have ⟨x, _, hx⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_countFam_inter σ hσ) this
  exact (M f).prop x hx

/-- There are at most `2 ^ 𝔠` countable subsets of `Ultrafilter ℕ`. -/
theorem mk_countable_set_le : #{ s : Set (Ultrafilter ℕ) // #s ≤ ℵ₀ } ≤ #(Ultrafilter ℕ) := by
  apply (Cardinal.mk_bounded_set_le_of_infinite _ _).trans
  rw [mk_ultrafilter_nat, ← power_mul, mul_eq_left]
  · exact cantor ℵ₀ |> le_of_lt
  · exact cantor ℵ₀ |> le_of_lt
  · exact aleph0_ne_zero

/-- The family of countably infinite subsets of `Ultrafilter ℕ` has cardinality `2 ^ 𝔠`. -/
theorem mk_index : #Index = #(Ultrafilter ℕ) := by
  apply eq_of_le_of_ge
  · apply le_trans _ mk_countable_set_le
    exact mk_subtype_mono fun s h => by simpa using h.right
  have ⟨s, hi, hc⟩ : Nonempty Index := by
    have : Index ≃ { s : Set (Ultrafilter ℕ) // #s = ℵ₀} := by
      refine Equiv.subtypeEquivProp ?_
      ext s
      refine ⟨fun h => ?_, fun h => ?_⟩
      · haveI : Infinite s := infinite_coe_iff.mpr h.left
        haveI : Countable s := Countable.to_subtype h.right
        exact mk_eq_aleph0 ↑s
      · refine ⟨?_, ?_⟩
        · refine infinite_coe_iff.mp (infinite_iff.mpr ?_)
          exact le_of_eq h.symm
        · haveI : Countable s := le_of_eq h |> mk_le_aleph0_iff.mp
          apply to_countable s
    apply Equiv.nonempty_congr this |>.mpr
    refine nonempty_subtype.mpr ?_
    apply le_mk_iff_exists_set.mp
    rw [mk_ultrafilter_nat]
    rw [← power_eq_two_power (le_of_lt <| cantor _) _ (le_of_lt <| cantor _)]
    · apply self_le_power
      apply le_trans (le_of_lt <| cantor _)
      apply power_le_power_left <;> simp
    · simp
  classical
  refine Function.Embedding.cardinal_le ⟨fun f => if f ∈ s then ⟨s \ {f}, ?_⟩ else ⟨s ∪ {f}, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact Infinite.diff hi (finite_singleton f)
    · exact Set.Countable.mono diff_subset hc
  · simpa using ⟨Infinite.mono (subset_insert _ _) hi, hc⟩
  intro f g h
  rcases Classical.em (f ∈ s) with hf | hf
  <;> rcases Classical.em (g ∈ s) with hg | hg
  <;> simp_all only [↓reduceIte, union_singleton, Subtype.mk.injEq]
  · apply (sdiff_right_inj _ _).mp h |> singleton_eq_singleton_iff.mp
    <;> simpa
  · grind
  · grind
  · exact insert_inj hf |>.mp h
