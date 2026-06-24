import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.NatAbs

import Settop.PInt
import Settop.Integer

open TopologicalSpace Set

@[reducible]
def P : Cond := {
  prop (a b) := Squarefree a ∧ Int.gcd a b = 1
  h1 := by
    intro a b c h hm;
    refine ⟨h.left, ?_⟩
    rw [mem_U_iff] at hm
    rcases hm with ⟨k, hm⟩
    have : c = b + a * k := by grind
    rw [this]
    simpa using h.right
  h2 := by
    intro a b h
    exact h.right
}

@[reducible]
def P' : Cond := {
  prop := fun a b => Prime a ∧ Int.gcd a b = 1
  h1 := by
    intro a b c h hc
    rw [mem_U_iff] at hc
    rcases hc with ⟨k,hc⟩
    have : c = b + k * a := by grind
    rw [this, Int.gcd_add_mul_right_right]
    exact h
  h2 := by
    intro a b h
    exact h.right
}

instance : TopologicalSpace ℤ := generateFrom (B P)

theorem lcm_eq_mul_div_gcd (a b : ℕ) : Nat.lcm a b = a * (b / Nat.gcd a b) := by
  rw [Nat.lcm, Nat.mul_div_assoc]
  exact Nat.gcd_dvd_right a b

theorem squarefree_mul_of_coprime {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hc : Nat.Coprime a b) : Squarefree (a * b) :=
  squarefree_mul_iff.mpr ⟨Nat.coprime_iff_isRelPrime.mp hc, ha, hb⟩

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (a.lcm b) := by
  rw [lcm_eq_mul_div_gcd a b]
  apply squarefree_mul_of_coprime
  · assumption
  · apply Squarefree.squarefree_of_dvd _ hb
    apply Nat.div_dvd_of_dvd
    exact Nat.gcd_dvd_right a b
  · apply Nat.coprime_iff_gcd_eq_one.mpr
    have hg : a.gcd b ∣ b := Nat.gcd_dvd_right a b
    have h1 : a.gcd (b / a.gcd b) ∣ b / a.gcd b := Nat.gcd_dvd_right _ _
    have h2 : a.gcd (b / a.gcd b) ∣ b := h1.trans (Nat.div_dvd_of_dvd hg)
    have h3 : a.gcd (b / a.gcd b) ∣ a.gcd b :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) h2
    apply Nat.isUnit_iff.mp (hb _ _)
    simpa [Nat.mul_div_cancel' hg] using Nat.mul_dvd_mul h3 h1

theorem basis : IsTopologicalBasis (B P) := by
  refine { exists_subset_inter := ?_, sUnion_eq := ?_, eq_generateFrom := rfl }
  · intro O hmemO O' hmemO' q hqmem
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at hmemO hmemO'
    rcases hmemO with ⟨a,b, ⟨sq_ab,abgcd⟩, heqO⟩
    rcases hmemO' with ⟨c,d, ⟨sq_cd, cdgcd⟩, heqO'⟩
    rw [heqO, heqO'] at hqmem ⊢
    use U (a.lcm c) q
    simp only [inter_U_eq_U_lcm hqmem, subset_refl, and_true]
    refine And.intro ?_ (mem_U_self (a.lcm c) q)
    apply mem_B
    simp only [Int.lcm, Cond.prop]
    apply And.intro
    · refine Int.squarefree_natCast.mpr ?_
      apply squarefree_lcm
      <;> simpa
    · refine Nat.Coprime.coprime_div_left ?_ (by simp)
      apply Nat.coprime_mul_iff_left.mpr
      refine And.intro
        (gcd_eq_one_of_mem_U abgcd (Set.mem_of_mem_inter_left hqmem))
        (gcd_eq_one_of_mem_U cdgcd (Set.mem_of_mem_inter_right hqmem))
  · apply sUnion_eq_univ_iff.mpr
    intro x
    use U 1 x
    apply And.intro _ (mem_U_self 1 x)
    apply mem_B
    simp [Cond.prop]

theorem eq_top : generateFrom (B P') = generateFrom (B P) := by
  apply le_antisymm
  · apply le_generateFrom
    intro s h
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at h
    rcases h with ⟨a, b, ⟨sqfree, ab_gcd⟩, eq⟩
    let fact : Finset ℤ := a.natAbs.primeFactors.image Int.ofNat
    have h {p} (h : p ∈ fact): p ∣ a := by
      simp only [fact, Finset.mem_image] at h
      rcases h with ⟨_, hp, heq⟩
      rw [← heq]
      apply Int.ofNat_dvd_left.mpr
      exact Nat.dvd_of_mem_primeFactors hp
    have h' : U a b = ⋂ p ∈ fact, U p b := by
      rw [Set.ext_iff]
      intro x
      apply Iff.trans _ mem_iInter₂.symm
      simp only [mem_U_iff]
      apply Iff.intro
      · intro ⟨k, xeq⟩ p mem
        rcases h mem with ⟨m, aeq⟩
        rw [aeq] at xeq
        use k*m
        grind
      · intro h
        have h2 : ∏ p ∈ fact, p ∣ x - b := by
          apply Finset.prod_dvd_of_coprime _ h
          intro p pmem q qmem neq
          simp only [Finset.coe_image, fact] at pmem qmem
          rcases pmem with ⟨p', prime_p', peq⟩
          rcases qmem with ⟨q', prime_q', qeq⟩
          simp at prime_p' prime_q'
          rw [Function.onFun_apply, ← peq, ← qeq]
          exact Nat.coprime_primes prime_p'.left prime_q'.left
            |>.mpr (by grind)
            |>.isCoprime
        apply dvd_trans _ h2
        apply Int.natAbs_dvd_natAbs.mp ⟨1, _⟩
        rw [Finset.prod_image, mul_one, ← Int.natAbsHom_apply]
        · rw [map_prod Int.natAbsHom]
          simpa using Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr sqfree)
        · exact Function.Injective.injOn Int.ofNat_injective
    rw [eq, h']
    letI := generateFrom (B P')
    apply isOpen_biInter_finset
    intro p mem
    apply isOpen_generateFrom_of_mem
    apply mem_B
    simp only [Cond.prop]
    apply And.intro
    · simp only [Finset.mem_image, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, fact] at mem
      rcases mem with ⟨_, ⟨prime, _⟩, eq⟩
      simpa [← eq] using Nat.prime_iff_prime_int.mp prime
    · apply Nat.eq_one_of_dvd_one
      exact ab_gcd ▸ Int.gcd_dvd_gcd_of_dvd_left b (h mem)
  · apply generateFrom_anti
    simp only [B, Set.mem_univ, Cond.prop, true_and, Set.setOf_subset_setOf, forall_exists_index,
      and_imp]
    intro _ p b prime gcd eq
    exact ⟨p, b, ⟨Prime.squarefree prime, gcd⟩, eq⟩

theorem connected : PreconnectedSpace ℤ := preconnectedSpace_of_isTopologicalBasis basis
