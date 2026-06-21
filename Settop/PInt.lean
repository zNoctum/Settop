import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Algebra.Group.Defs

def PInt := { z : Int // 0 < z }
notation "ℤ+" => PInt

@[simp]
def PInt.pos (z : PInt) : 0 < z.val := z.property

instance (n : Nat) : OfNat PInt (n + 1) :=
  ⟨⟨n + 1, by simp⟩⟩

instance coePIntInt : Coe PInt Int :=
  ⟨Subtype.val⟩

instance : Repr PInt :=
  ⟨fun n n' => reprPrec n.1 n'⟩

instance : DecidableEq ℤ+ := Subtype.instDecidableEq

@[simp]
theorem PInt.val_mk (n : Int) (h : 0 < n) : (⟨n, h⟩ : PInt).val = n := rfl

def PInt.lcm (a b : PInt) : PInt := ⟨Int.lcm a b, by
  simp only [Int.natCast_pos, Int.lcm_pos_iff];
  apply And.intro (Ne.symm (ne_of_lt a.property)) (Ne.symm (ne_of_lt b.property))
⟩

theorem PInt.val_mul_pos {a b : ℤ+} : 0 < a.val * b.val := by simp [Int.mul_pos]

theorem PInt.natAbs_val {a : ℤ+} : a.val.natAbs = a.val := by
  apply Int.natAbs_of_nonneg
  exact le_of_lt a.property
