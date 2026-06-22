import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Connected.Clopen

import Settop.PInt

open Set

def U (a b : ℤ) : Set ℤ := {x ∈ univ | a ∣ x - b }

class Cond where
  prop : ℤ → ℤ → Prop
  h1 : ∀ {a b c}, prop a b → c ∈ U a b → prop a c
  h2 : ∀ {a b}, prop a b → Int.gcd a b = 1

def B (P : Cond) := {
    O ∈ univ | ∃a b : ℤ,
      P.prop a b ∧
      O = U a b
  }

theorem mem_B {a b : ℤ} {P : Cond} (h : P.prop a b) : U a b ∈ B P := by
  simp only [B, U, mem_univ, true_and, mem_setOf_eq]
  use a, b

theorem mem_U_iff {a b x : ℤ} : x ∈ U a b ↔ (a : ℤ) ∣ x - b := by
  simp only [U, mem_univ, true_and, mem_setOf_eq]

theorem mem_U_self (a b : ℤ) : b ∈ U a b := by
  apply mem_U_iff.mpr
  use 0
  simp

theorem gcd_eq_one_of_mem_U {a b q : ℤ} (hc : Int.gcd a b = 1) (h : q ∈ U a b) :
    Int.gcd a q = 1 := by
  simp only [U, mem_univ, true_and, mem_setOf_eq] at h
  simpa [hc] using Int.gcd_add_right_right_of_dvd b h

theorem U_eq_of_mem {a b q : ℤ} (hm : q ∈ U a b) : U a q = U a b := by
  apply Eq.symm (Set.ext _)
  intro x
  simp only [mem_U_iff] at *
  apply Int.dvd_iff_dvd_of_dvd_sub _
  simpa using hm

theorem mem_U_of_dvd {a b c : ℤ} (hm : n ∈ U a b) (hd : c ∣ a) : n ∈ U c b := by
  rw [mem_U_iff] at hm ⊢
  apply Int.dvd_trans hd hm

theorem inter_U_eq_U_lcm {a b c d q : ℤ} (h : q ∈ U a b ∩ U c d) :
    U a b ∩ U c d = U (a.lcm c) q := by
  apply Eq.symm (ext _)
  intro x
  simp only [mem_inter_iff, mem_U_iff] at h ⊢
  apply Iff.trans Int.coe_lcm_dvd_iff
  apply Iff.intro <;> intro ⟨hab, hcd⟩
  · have := Int.dvd_add hab h.left
    have := Int.dvd_add hcd h.right
    grind
  · have := Int.dvd_sub hab h.left
    have := Int.dvd_sub hcd h.right
    grind

theorem le_mul_of_pos {a b c : ℤ} (h : a ≤ c) (hh : 0 ≤ c) (h' : 0 < b) : a ≤ b * c := by
  rw [← one_mul a, mul_comm, mul_comm b]
  apply Int.mul_le_mul
  <;> grind

theorem inter_U_nonempty_iff {a b c d : ℤ} :
    (U a b ∩ U c d).Nonempty ↔ b % a.gcd c = d % a.gcd c := by
  apply Iff.intro
  · intro ⟨x, hab, hcd⟩
    simp only [mem_U_iff] at hab hcd
    have h : ↑(a.gcd c) ∣ b - d := by
      simpa using Int.dvd_sub
        (dvd_trans (Int.gcd_dvd_right a c) hcd)
        (dvd_trans (Int.gcd_dvd_left a c) hab)
    rcases h with ⟨_, h⟩
    simp [h, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  · intro h
    apply Set.inter_nonempty.mpr
    have : ↑(Int.gcd a c) ∣ b - d := by
      apply Int.dvd_of_emod_eq_zero
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h
      exact h
    rcases this with ⟨r,h⟩
    rw [Int.gcd_eq_gcd_ab, Int.add_mul] at h
    have : b - a * Int.gcdA a c * r = d + c * Int.gcdB a c * r := by
      grind
    let n := (Int.gcdA a c * r).natAbs
    use b - a * Int.gcdA a c * r + a * c * n
    apply And.intro <;> apply mem_U_iff.mpr
    <;> simp only [this]
    · use - Int.gcdA a c * r + c * n
      grind
    · use Int.gcdB a c * r + a * n
      grind

open TopologicalSpace

variable {P : Cond}
variable [TopologicalSpace ℤ]

theorem exists_U_of_mem_isOpen {O : Set ℤ} {x : ℤ} (hb : IsTopologicalBasis (B P))
    (h : IsOpen O) (h' : x ∈ O) : ∃ a b, U a b ⊆ O ∧ P.prop a b ∧ x ∈ U a b := by
  rcases (IsTopologicalBasis.isOpen_iff hb).mp h x h' with ⟨O',⟨memB, mem, sub⟩⟩
  simp only [B, mem_univ, true_and, mem_setOf_eq] at memB
  rcases memB with ⟨a, b, hl, hr⟩
  exact ⟨a, b, hr ▸ sub, hl, hr ▸ mem⟩


theorem mul_mem_closure_U (hb : IsTopologicalBasis (B P)) (a b k : ℤ) :
    a * k ∈ closure (U a b) := by
  apply mem_closure_iff.mpr
  intro O hO acmem
  rcases exists_U_of_mem_isOpen hb hO acmem with ⟨t, b', hsub, ptb', mem'⟩
  apply Nonempty.mono <| inter_subset_inter hsub (subset_refl (U a b))
  rw [inter_U_nonempty_iff]
  have := Int.gcd_dvd_gcd_mul_left_right t a k
  rw [mul_comm, P.h2 (P.h1 ptb' mem'), Nat.dvd_one] at this
  simp [this]

theorem inter_closure_U_nonempty (hb : IsTopologicalBasis (B P)) (a b c d : ℤ) :
    (closure (U a b) ∩ closure (U c d)).Nonempty := by
  use Int.lcm a c
  rw [Set.mem_inter_iff]
  apply And.intro
  · rcases Int.dvd_lcm_left a c with ⟨k, keqac⟩
    rw [keqac]
    exact mul_mem_closure_U hb a b k
  · rcases Int.dvd_lcm_left c a with ⟨k, keqac⟩
    rw [Int.lcm_comm a c, keqac]
    exact mul_mem_closure_U hb c d k

theorem exists_closure_U_subset_of_isOpen {o : Set ℤ} (hb : IsTopologicalBasis (B P))
    (ho : IsOpen o) (hone : o.Nonempty) : ∃ a b, closure (U a b) ⊆ closure o := by
  rcases hone with ⟨_, mem⟩
  rcases exists_U_of_mem_isOpen hb ho mem with ⟨a, b, hsub, _, _⟩
  use a, b
  exact closure_mono hsub

theorem preconnectedSpace_of_isTopologicalBasis (hb : IsTopologicalBasis (B P)) :
    PreconnectedSpace ℤ := by
  apply preconnectedSpace_iff_clopen.mpr
  intro O hcoo
  have hcooc : IsClopen Oᶜ := by simp; grind
  by_contra! ⟨hne, hne'⟩
  rw [← Set.nonempty_compl] at hne'
  have cl {s : Set ℤ} (hcl : IsClopen s) : closure s = s := by
    apply closure_eq_iff_isClosed.mpr
    exact IsClopen.isClosed hcl
  have : ¬(closure O ∩ closure Oᶜ).Nonempty := by
    rw [cl hcoo, cl hcooc]
    apply Set.not_nonempty_iff_eq_empty.mpr
    exact inter_compl_self O
  apply this
  rcases exists_closure_U_subset_of_isOpen hb hcoo.right  hne  with ⟨a, b, hsub⟩
  rcases exists_closure_U_subset_of_isOpen hb hcooc.right hne' with ⟨c, d, hsub'⟩
  apply Nonempty.mono (Set.inter_subset_inter hsub hsub')
  exact inter_closure_U_nonempty hb a b c d
