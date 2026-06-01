import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
import Mathlib.Data.Nat.GCD.Basic

open TopologicalSpace


def U (a b : ℕ+) : Set ℕ+ := {n ∈ Set.univ | ∃ k : ℕ, n = (b % a) + k*a }

def B := {
    O ∈ Set.univ | ∃a b : ℕ+,
      Nat.Coprime a b ∧
      U a b = O
  }

instance : TopologicalSpace ℕ+ := generateFrom B

def PNat.lcm (a b : ℕ+) : ℕ+ := ⟨Nat.lcm a b, by apply Nat.lcm_pos <;> simp⟩

lemma CoprimeU {a b q : ℕ+} (hc : Nat.Coprime a b) (h : q ∈ U a b) : Nat.Coprime a q := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at h
  rcases h with ⟨k,h⟩
  simp only [Nat.Coprime, h, Nat.mod_eq_sub_div_mul, dvd_mul_left, Nat.gcd_add_right_right_of_dvd]
  rw [Nat.gcd_sub_mul_right_right, hc]
  exact Nat.div_mul_le_self ↑b ↑a

lemma eqU {a b q : ℕ+} (hm : q ∈ U a b) : U a q = U a b := by
  apply Set.ext
  intro n
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at hm ⊢
  rcases hm with ⟨l, hm⟩
  apply Iff.intro <;> intro ⟨k, h⟩
  · rw [hm, Nat.add_mul_mod_self_right, Nat.mod_mod] at h
    exact ⟨k, h⟩
  · rw [hm, Nat.add_mul_mod_self_right, Nat.mod_mod]
    exact ⟨k, h⟩

lemma dvdU {a b c : ℕ+} (hm : n ∈ U a b) (hd : c.val ∣ a) : n ∈ U c b := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at *
  rcases hm with ⟨k, hm⟩
  rw [dvd_def] at hd
  rcases hd with ⟨l, hd⟩

  rw [hd, Nat.mod_mul] at hm
  rw [hm, Nat.add_assoc]
  use (↑b / ↑c % l + k * l)
  apply Nat.add_left_cancel_iff.mpr
  rw [← Nat.mul_assoc, mul_comm k ↑c, Nat.mul_assoc, ← Nat.left_distrib, Nat.mul_comm _ ↑c]


lemma t' {a b c d q : ℕ+} (h : q ∈ U a b ∩ U c d) : U a b ∩ U c d = U (PNat.lcm a c) q := by
  refine Eq.symm (Set.ext ?_)
  intro n
  rw [Set.mem_inter_iff] at h ⊢
  apply Iff.intro
  · intro hmem
    apply And.intro <;>
      simp only [←eqU h.left, ← eqU h.right] <;>
      apply dvdU hmem
    · apply Nat.Dvd.dvd.nat_lcm_right
      apply Nat.dvd_refl
    · apply Nat.Dvd.dvd.nat_lcm_left
      apply Nat.dvd_refl
  · intro ⟨hab, hcd⟩
    · --
      rw [← eqU h.left] at hab h
      rw [← eqU h.right] at hcd h
      simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq] at *
      rcases hab with ⟨k, hab⟩
      rcases hcd with ⟨l, hcd⟩







lemma Umem (a b : ℕ+) : b ∈ U a b := by
  simp only [U, Set.mem_univ, true_and, Set.mem_setOf_eq]
  use (b / a)
  exact Eq.symm (Nat.mod_add_div' ↑b ↑a)

lemma memU {a b : ℕ+} (h : Nat.Coprime a b) : U a b ∈ B := by
  simp only [B, U, Set.mem_univ, true_and, Set.mem_setOf_eq]
  use a, b

lemma t : IsTopologicalBasis B := by
  refine { exists_subset_inter := ?_, sUnion_eq := ?_, eq_generateFrom := rfl }
  · intro O hmemO O' hmemO' q hqmem
    simp only [B, Set.mem_univ, true_and, Set.mem_setOf_eq] at hmemO hmemO'
    rcases hmemO with ⟨a,b, abgcd, heqO⟩
    rcases hmemO' with ⟨c,d, cdgcd, heqO'⟩
    rw [←heqO, ←heqO'] at hqmem ⊢
    use U (PNat.lcm a c) q
    simp only [t' hqmem, subset_refl, and_true]
    refine And.intro ?_ (Umem (a.lcm c) q)
    apply memU
    simp only [PNat.lcm, Nat.lcm, PNat.mk_coe, Nat.coprime_iff_gcd_eq_one]
    refine Nat.Coprime.coprime_div_left ?_ (by simp)
    apply Nat.coprime_mul_iff_left.mpr
    refine And.intro
      (CoprimeU abgcd (Set.mem_of_mem_inter_left hqmem))
      (CoprimeU cdgcd (Set.mem_of_mem_inter_right hqmem))
  · apply Set.sUnion_eq_univ_iff.mpr
    intro n
    use U 1 n
    refine And.intro ?_ (Umem 1 n)
    apply memU
    norm_cast
    exact Nat.gcd_one_left ↑n
