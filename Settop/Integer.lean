import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Connected.Clopen

import Settop.PInt

def U (a b : ℤ+) : Set ℤ+ := {x ∈ Set.univ | (a : ℤ) ∣ x - b }

class Cond where
  prop : ℤ+ → ℤ+ → Prop
  h1 : ∀ {a b c}, prop a b → c ∈ U a b → prop a c
  h2 : ∀ {a b}, prop a b → Int.gcd a b = 1

def B (P : Cond) := {
    O ∈ Set.univ | ∃a b : ℤ+,
      P.prop a b ∧
      O = U a b
  }

theorem mem_B {a b : ℤ+} {P : Cond} (h : P.prop a b) : U a b ∈ B P := by
  simp only [B, U, Set.mem_univ, true_and, Set.mem_setOf_eq]
  use a, b

theorem mem_U_iff {a b x : ℤ+} : x ∈ U a b ↔ (a : ℤ) ∣ x - b := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq]

theorem mem_U_self (a b : ℤ+) : b ∈ U a b := by
  apply mem_U_iff.mpr
  use 0
  grind

theorem gcd_eq_one_of_mem_U {a b q : ℤ+} (hc : Int.gcd a b = 1) (h : q ∈ U a b) :
    Int.gcd a q = 1 := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at h
  simpa [hc] using Int.gcd_add_right_right_of_dvd b h

theorem U_eq_of_mem {a b q : ℤ+} (hm : q ∈ U a b) : U a q = U a b := by
  apply Set.ext
  intro x
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at hm ⊢
  apply Iff.intro
  <;> intro h
  · simpa using Int.dvd_add hm h
  · simpa using Int.dvd_sub h hm

theorem mem_U_of_dvd {a b c : ℤ+} (hm : n ∈ U a b) (hd : c.val ∣ a) : n ∈ U c b := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at *
  rcases hm with ⟨k, hm⟩
  rw [dvd_def] at hd
  rcases hd with ⟨l, hd⟩
  rw [hm, hd]
  use k * l
  grind

theorem inter_U_eq_U_lcm {a b c d q : ℤ+} (h : q ∈ U a b ∩ U c d) :
    U a b ∩ U c d = U (PInt.lcm a c) q := by
  apply Eq.symm (Set.ext _)
  intro x
  rw [Set.mem_inter_iff] at h ⊢
  apply Iff.intro
  · intro hmem
    apply And.intro
      <;> simp only [←U_eq_of_mem h.left, ← U_eq_of_mem h.right]
      <;> apply mem_U_of_dvd hmem
      <;> apply Int.natAbs_dvd_natAbs.mp
    · apply Nat.Dvd.dvd.nat_lcm_right
      apply Nat.dvd_refl
    · apply Nat.Dvd.dvd.nat_lcm_left
      apply Nat.dvd_refl
  · intro ⟨hab, hcd⟩
    · rw [← U_eq_of_mem h.left] at hab h
      rw [← U_eq_of_mem h.right] at hcd h
      simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at *
      have : (Int.lcm a c : ℤ) ∣ x - q := by
        apply Int.natAbs_dvd_natAbs.mp
        apply Nat.lcm_dvd
        <;> simp [hab, hcd]
      exact Int.natAbs_dvd.mp this

theorem le_mul_of_pos {a b c : ℤ} (h : a ≤ c) (hh : 0 ≤ c) (h' : 0 < b) : a ≤ b * c := by
  rw [← one_mul a, mul_comm, mul_comm b]
  apply Int.mul_le_mul
  <;> grind

theorem inter_U_nonempty_iff {a b c d : ℤ+} :
    (U a b ∩ U c d).Nonempty ↔ (b : ℤ) % (Int.gcd a c) = d % (Int.gcd a c) := by
  apply Iff.intro
  <;> intro h
  · rcases h with ⟨x, ⟨_, k, hab⟩, ⟨_, l, hcd⟩⟩
    have : (Int.gcd a c : ℤ) ∣ b - d := by
      rw [(by grind : b - d = l * ↑c - k * ↑a)]
      refine Int.dvd_sub ?_ ?_
      <;> apply Int.dvd_mul_of_dvd_right
      · exact Int.gcd_dvd_right ↑a ↑c
      · exact Int.gcd_dvd_left ↑a ↑c
    rcases this with ⟨m, bd⟩
    simp [bd, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  · apply Set.inter_nonempty.mpr
    have : ↑(Int.gcd a c) ∣ b.val - d.val := by
      apply Int.dvd_of_emod_eq_zero
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h
      exact h
    rcases this with ⟨r,h⟩
    rw [Int.gcd_eq_gcd_ab, Int.add_mul] at h
    have : b - a * Int.gcdA a c * r = d + c * Int.gcdB a c * r := by
      grind
    let n := Int.natAbs (Int.gcdA a c * r)
    have pos : 0 < b - a * Int.gcdA a c * r + a * c * n := by
      dsimp only [n]
      apply Int.sub_lt_iff.mp
      apply Int.sub_lt_sub_of_lt_of_le b.prop
      rw [mul_assoc, mul_assoc]
      apply (Int.mul_le_mul_left a.prop).mpr
      refine le_mul_of_pos ?_ (by exact Int.natCast_nonneg (Int.gcdA a c * r).natAbs) c.prop
      exact Int.le_natAbs
    use ⟨b - a * Int.gcdA a c * r + a * c * n, pos⟩
    apply And.intro
    <;> simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq, this]
    · use - Int.gcdA a c * r + c * n
      grind
    · use Int.gcdB a c * r + a * n
      grind

theorem PInt.dvd_lcm_left (a b : ℤ+) : ∃ m : ℤ+, Int.lcm a b = m.val * a.val := by
  rcases Int.dvd_lcm_left a b with ⟨k, keqac⟩
  rw [mul_comm] at keqac
  have h : 0 < k := by
    have := Int.lcm_pos (ne_of_lt a.prop).symm (ne_of_lt b.prop).symm
    have : 0 < k * ↑a := by grind
    exact Int.pos_of_mul_pos_left this a.prop
  use ⟨k, h⟩

theorem subset_nonempty {α : Type*} {r s : Set α}
    (h : r ⊆ s) (hn : r.Nonempty) : s.Nonempty := by
  obtain ⟨x, hx⟩ := hn
  exact ⟨x, h hx⟩

open TopologicalSpace
variable [TopologicalSpace ℤ+]
variable {P : Cond}

theorem exists_U_of_mem_isOpen {O : Set ℤ+} {x : ℤ+} (hb : IsTopologicalBasis (B P))
    (h : IsOpen O) (h' : x ∈ O) : ∃ a b, U a b ⊆ O ∧ P.prop a b ∧ x ∈ U a b := by
  rcases (IsTopologicalBasis.isOpen_iff hb).mp h x h' with ⟨O',⟨memB, mem, sub⟩⟩
  simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at memB
  rcases memB with ⟨a, b, hl, hr⟩
  exact ⟨a, b, hr ▸ sub, hl, hr ▸ mem⟩

theorem mul_mem_closure_U (hb : IsTopologicalBasis (B P)) (a b k : ℤ+) :
    ⟨k.val * a.val, PInt.val_mul_pos⟩ ∈ closure (U a b) := by
  apply mem_closure_iff.mpr
  intro O hO acmem
  rcases exists_U_of_mem_isOpen hb hO acmem with ⟨t, b', hsub, ptb', mem'⟩
  apply subset_nonempty (Set.inter_subset_inter hsub (Set.Subset.refl (U a b)))
  rw [inter_U_nonempty_iff]
  have := Int.gcd_dvd_gcd_mul_left_right t a k
  rw [P.h2 (P.h1 ptb' mem'), Nat.dvd_one] at this
  simp [this]

theorem inter_closure_U_nonempty (hb : IsTopologicalBasis (B P)) (a b c d : ℤ+) :
    (closure (U a b) ∩ closure (U c d)).Nonempty := by
  use ⟨Int.lcm a c, by
    apply Int.natCast_pos.mpr
    exact Int.lcm_pos (ne_of_lt a.prop).symm (ne_of_lt c.prop).symm⟩
  rw [Set.mem_inter_iff]
  apply And.intro
  · rcases PInt.dvd_lcm_left a c with ⟨k, keqac⟩
    simp only [keqac]
    refine mul_mem_closure_U hb a b k
  · rcases PInt.dvd_lcm_left c a with ⟨k, keqac⟩
    simp only [Int.lcm_comm ↑a ↑c, keqac]
    refine mul_mem_closure_U hb c d k

theorem exists_closure_U_subset_of_isOpen {O : Set ℤ+} (hb : IsTopologicalBasis (B P))
    (hO : IsOpen O) (hOne : O.Nonempty) : ∃ a b, closure (U a b) ⊆ closure O := by
  rcases hOne with ⟨x, xmem⟩
  rcases exists_U_of_mem_isOpen hb hO xmem with ⟨a, b, hsub, _, _⟩
  use a, b
  apply closure_mono
  exact hsub

theorem preconnectedSpace_of_isTopologicalBasis (hb : IsTopologicalBasis (B P)) :
    PreconnectedSpace ℤ+ := by
  apply preconnectedSpace_iff_clopen.mpr
  intro O hcoo
  let O' := Oᶜ
  have hcooc : IsClopen Oᶜ := by simp; grind
  by_contra! ⟨hne, hne'⟩
  rw [← Set.nonempty_compl] at hne'
  have clO : closure O = O := by
    apply closure_eq_iff_isClosed.mpr
    exact IsClopen.isClosed hcoo
  have clO' : closure Oᶜ = Oᶜ := by
    apply closure_eq_iff_isClosed.mpr
    exact IsClopen.isClosed hcooc
  rcases exists_closure_U_subset_of_isOpen hb hcoo.right  hne  with ⟨a, b, hsub⟩
  rcases exists_closure_U_subset_of_isOpen hb hcooc.right hne' with ⟨c, d, hsub'⟩
  have : (closure O ∩ closure Oᶜ).Nonempty := by
    apply subset_nonempty (Set.inter_subset_inter hsub hsub')
    exact inter_closure_U_nonempty hb a b c d
  have emp_int : ¬(closure O ∩ closure O').Nonempty := by
    rw [clO, clO']
    apply Set.not_nonempty_iff_eq_empty.mpr
    grind
  exact emp_int this
