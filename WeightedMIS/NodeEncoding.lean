module

public import WeightedMIS.Expanded

/-!
# Explicit numeric encodings of expanded states

All equivalences here have executable maps. In particular, no enumeration by
classical choice is used to assign vertex IDs. Signature tuples use positional
base-(4m+1) encoding.
-/

@[expose] public section

namespace WeightedMIS.NodeEncoding

open WeightedMIS.Walks WeightedMIS.Expanded

def boolEquiv : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i.val = 1)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Signed states have concrete numeric IDs in [0,2r]. -/
def stateEquiv (r : ℕ) : State (Fin r) ≃ Fin (2 * r + 1) :=
  (Equiv.optionCongr ((Equiv.prodCongr (Equiv.refl (Fin r)) boolEquiv).trans finProdFinEquiv)).trans
    ((finSuccEquiv (r * 2)).symm.trans (finCongr (by omega)))

/-- Positional numeral encoding of a signature tuple. -/
def boxEquiv (d m : ℕ) : Box (Fin d) m ≃ Fin ((4 * m + 1) ^ d) := finFunctionFinEquiv

/-- The parity bit already has the computational representation Fin 2. -/
def parityEquiv : ZMod 2 ≃ Fin 2 := Equiv.refl _

/-- Number of encoded vertices. -/
def nodeCount (r d m : ℕ) : ℕ := 2 * (4 * m + 1) ^ d * (1 + (2 * r + 1) ^ 2)

/-- Expose the hub/working cases as products for positional encoding. -/
def nodeShape (r d m : ℕ) : Node (Fin r) (Fin d) m ≃
    ((Box (Fin d) m × ZMod 2) ⊕
      (State (Fin r) × State (Fin r) × Box (Fin d) m × ZMod 2)) where
  toFun x := match x with
    | .hub z p => .inl (z, p)
    | .work a v z p => .inr (a, v, z, p)
  invFun x := match x with
    | .inl (z, p) => .hub z p
    | .inr (a, v, z, p) => .work a v z p
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- A bijective executable numeric vertex encoding, not an arbitrary Fintype
choice. Its inverse uses ordinary quotient/remainder operations. -/
def nodeEquiv (r d m : ℕ) : Node (Fin r) (Fin d) m ≃ Fin (nodeCount r d m) :=
  (nodeShape r d m).trans
    (((Equiv.prodCongr (boxEquiv d m) parityEquiv).trans finProdFinEquiv).sumCongr
      ((Equiv.prodCongr (stateEquiv r)
        ((Equiv.prodCongr (stateEquiv r)
          ((Equiv.prodCongr (boxEquiv d m) parityEquiv).trans finProdFinEquiv)).trans
            finProdFinEquiv)).trans finProdFinEquiv) |>.trans
      (finSumFinEquiv.trans (finCongr (by unfold nodeCount; ring))))

@[simp] theorem decode_encode (r d m : ℕ) (v : Node (Fin r) (Fin d) m) :
    (nodeEquiv r d m).symm (nodeEquiv r d m v) = v := (nodeEquiv r d m).symm_apply_apply v

@[simp] theorem encode_decode (r d m : ℕ) (i : Fin (nodeCount r d m)) :
    nodeEquiv r d m ((nodeEquiv r d m).symm i) = i := (nodeEquiv r d m).apply_symm_apply i

/-- Numeric IDs have binary length bounded by the length of the state count. -/
theorem node_id_bits (r d m : ℕ) (v : Node (Fin r) (Fin d) m) :
    (nodeEquiv r d m v).val.size ≤ (nodeCount r d m).size :=
  Nat.size_le_size (Nat.le_of_lt (nodeEquiv r d m v).isLt)

/-- Every stored coordinate uses at most the binary length of 4m+1 bits. -/
theorem coordinate_bits {d m : ℕ} (z : Box (Fin d) m) (i : Fin d) :
    (z i).val.size ≤ (4 * m + 1).size := Nat.size_le_size (Nat.le_of_lt (z i).isLt)

end WeightedMIS.NodeEncoding
