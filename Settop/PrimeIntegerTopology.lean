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

import Settop.PInt
import Settop.Integer

open TopologicalSpace

@[reducible]
def P : Cond := {
  prop (a b) := Squarefree a.val ∧ Int.gcd a b = 1
  h1 := by
    intro a b c h hm;
    refine ⟨h.left, ?_⟩
    rw [mem_U_iff] at hm
    rcases hm with ⟨k, hm⟩
    have : c.val = b + a * k := by grind
    rw [this]
    simpa using h.right
  h2 := by
    intro a b h
    exact h.right
}

@[reducible]
def P' : Cond := {
  prop := fun a b => Prime a.val ∧ Int.gcd a b = 1
  h1 := by
    intro a b c h hc
    rw [mem_U_iff] at hc
    rcases hc with ⟨k,hc⟩
    have : c.val = b + k * a := by grind
    rw [this, Int.gcd_add_mul_right_right]
    exact h
  h2 := by
    intro a b h
    exact h.right
}

instance : TopologicalSpace ℤ+ := generateFrom (B P)

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
    have hg : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have h1 : Nat.gcd a (b / Nat.gcd a b) ∣ b / Nat.gcd a b := Nat.gcd_dvd_right _ _
    have h2 : Nat.gcd a (b / Nat.gcd a b) ∣ b := h1.trans (Nat.div_dvd_of_dvd hg)
    have h3 : Nat.gcd a (b / Nat.gcd a b) ∣ Nat.gcd a b :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) h2
    have h4 : Nat.gcd a (b / Nat.gcd a b) * Nat.gcd a (b / Nat.gcd a b) ∣ b := by
      have := Nat.mul_dvd_mul h3 h1
      rwa [Nat.mul_div_cancel' hg] at this
    exact Nat.isUnit_iff.mp (hb _ h4)

theorem basis : IsTopologicalBasis (B P) := by
  refine { exists_subset_inter := ?_, sUnion_eq := ?_, eq_generateFrom := rfl }
  · intro O hmemO O' hmemO' q hqmem
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at hmemO hmemO'
    rcases hmemO with ⟨a,b, ⟨sq_ab,abgcd⟩, heqO⟩
    rcases hmemO' with ⟨c,d, ⟨sq_cd, cdgcd⟩, heqO'⟩
    rw [heqO, heqO'] at hqmem ⊢
    use U (PInt.lcm a c) q
    simp only [inter_U_eq_U_lcm hqmem, subset_refl, and_true]
    refine And.intro ?_ (mem_U_self (a.lcm c) q)
    apply mem_B
    simp only [PInt.lcm, Int.lcm, Cond.prop]
    apply And.intro
    · refine Int.squarefree_natCast.mpr ?_
      apply squarefree_lcm
      <;> simpa
    · refine Nat.Coprime.coprime_div_left ?_ (by simp)
      apply Nat.coprime_mul_iff_left.mpr
      refine And.intro
        (gcd_eq_one_of_mem_U abgcd (Set.mem_of_mem_inter_left hqmem))
        (gcd_eq_one_of_mem_U cdgcd (Set.mem_of_mem_inter_right hqmem))
  · apply Set.sUnion_eq_univ_iff.mpr
    intro x
    use U ⟨1, by simp⟩ x
    refine And.intro ?_ (mem_U_self ⟨1, by simp⟩ x)
    apply mem_B
    simp [Cond.prop]

theorem eq_top : generateFrom (B P') = generateFrom (B P) := by
  apply le_antisymm
  · apply le_generateFrom
    intro s h
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at h
    rcases h with ⟨a, b, ⟨sqfree, ab_gcd⟩, eq⟩
    let fact : Finset ℤ+ := a.val.natAbs.primeFactors.attach.image
      (fun p => ⟨(p.val : ℤ),  by simp [Nat.pos_of_mem_primeFactors p.prop]⟩)
    have h {p} (h : p ∈ fact): p.val ∣ a := by
      simp only [fact, Finset.mem_image, Finset.mem_attach, true_and] at h
      obtain ⟨⟨p', hp'⟩, rfl⟩ := h
      exact PInt.natAbs_val ▸ Int.ofNat_dvd_left.mpr (Nat.mem_primeFactors.mp hp').2.1
    have h' : U a b = ⋂ p ∈ fact, U p b := by
      rw [@Set.ext_iff]
      intro x
      simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq, Set.mem_iInter]
      apply Iff.intro
      · intro ⟨k, xeq⟩ p mem
        rcases h mem with ⟨m, aeq⟩
        rw [aeq] at xeq
        use k*m
        grind
      · intro h
        have h1 : Squarefree a.val.natAbs := Int.squarefree_natAbs.mpr sqfree
        have h2 : ∏ p ∈ fact, p.val ∣ x - b := by
          apply Finset.prod_dvd_of_coprime _ h
          intro p pmem q qmem neq
          simp only [Finset.coe_image, Finset.coe_attach, Set.image_univ, Set.mem_range,
            Subtype.exists, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, fact] at pmem qmem
          rcases pmem with ⟨p', ⟨prime_p', _⟩, peq⟩
          rcases qmem with ⟨q', ⟨prime_q', _⟩, qeq⟩
          have : p' ≠ q' := by
            simp [← peq, ← qeq] at neq
            grind
          rw [Function.onFun_apply, ← peq, ← qeq]
          exact Nat.coprime_primes prime_p' prime_q' |>.mpr this |>.isCoprime
        have h3 : ∏ p ∈ fact, p.val = a.val.natAbs := by
          dsimp only [fact]
          rw [Finset.prod_image, Finset.prod_attach]
          · nth_rw 2 [← Nat.prod_primeFactors_of_squarefree h1]
            simp
          · refine Function.Injective.injOn ?_
            rw [@Function.injective_iff_pairwise_ne]
            intro _ _ _
            rw [Function.onFun_apply]
            grind
        rw [h3] at h2
        grind
    rw [eq, h']
    letI := generateFrom (B P')
    apply isOpen_biInter_finset
    intro p mem
    apply isOpen_generateFrom_of_mem
    simp only [B, Set.mem_univ, Cond.prop, true_and, Set.mem_setOf_eq]
    use p, b
    apply And.intro (And.intro _ _) (rfl)
    · simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
      Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, fact] at mem
      rcases mem with ⟨p', ⟨prime_p', _⟩, eq⟩
      simpa [← eq] using Nat.prime_iff_prime_int.mp prime_p'
    · apply Nat.eq_one_of_dvd_one
      exact ab_gcd ▸ Int.gcd_dvd_gcd_of_dvd_left b (h mem)
  · apply generateFrom_anti
    simp only [B, Set.mem_univ, Cond.prop, true_and, Set.setOf_subset_setOf, forall_exists_index,
      and_imp]
    intro s p b prime gcd eq
    exact ⟨p, b, ⟨Prime.squarefree prime, gcd⟩, eq⟩

theorem connected : PreconnectedSpace ℤ+ := preconnectedSpace_of_isTopologicalBasis basis
