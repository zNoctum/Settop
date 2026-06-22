import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Connected.Clopen

import Settop.PInt
import Settop.Integer

open TopologicalSpace

@[reducible]
def P : Cond := {
  prop := fun a b => Int.gcd a b = 1
  h1 := by
    intro a b c h hc
    rw [mem_U_iff] at hc
    rcases hc with ⟨k,hc⟩
    have : c = b + k * a := by grind
    rw [this, Int.gcd_add_mul_right_right]
    exact h
  h2 := by
    intro a b h
    exact h
}

instance : TopologicalSpace ℤ := generateFrom (B P)

theorem basis : IsTopologicalBasis (B P) := by
  refine { exists_subset_inter := ?_, sUnion_eq := ?_, eq_generateFrom := rfl }
  · intro O hmemO O' hmemO' q hqmem
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at hmemO hmemO'
    rcases hmemO with ⟨a,b, abgcd, heqO⟩
    rcases hmemO' with ⟨c,d, cdgcd, heqO'⟩
    rw [heqO, heqO'] at hqmem ⊢
    use U (a.lcm c) q
    simp only [inter_U_eq_U_lcm hqmem, subset_refl, and_true]
    apply And.intro _ (mem_U_self (a.lcm c) q)
    apply mem_B
    simp only [Int.lcm]
    apply Nat.Coprime.coprime_div_left _ (by simp)
    apply Nat.coprime_mul_iff_left.mpr
    refine And.intro
      (gcd_eq_one_of_mem_U abgcd (Set.mem_of_mem_inter_left hqmem))
      (gcd_eq_one_of_mem_U cdgcd (Set.mem_of_mem_inter_right hqmem))
  · apply Set.sUnion_eq_univ_iff.mpr
    intro x
    use U 1 x
    apply And.intro _ (mem_U_self 1 x)
    apply mem_B
    exact Int.gcd_one_left ↑x

theorem connected : PreconnectedSpace ℤ := preconnectedSpace_of_isTopologicalBasis basis
