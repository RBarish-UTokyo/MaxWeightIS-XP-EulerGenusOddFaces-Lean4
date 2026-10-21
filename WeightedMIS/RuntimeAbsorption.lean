module

public import WeightedMIS.EncodingCost
public import WeightedMIS.RegisterMachineFrames

/-!
# Preserving the parameter exponent under logarithmic machine overhead

The address and physical-stack overhead adds one absolute power of the graph
size and one power of the weight-bit bound. The parameter-dependent exponent
is not multiplied by a simulation constant.
-/

@[expose] public section

namespace WeightedMIS.RuntimeAbsorption

open WeightedMIS.EncodingCost WeightedMIS.RegisterMachine WeightedMIS.PointerMemory

theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr a.lt_two_pow_self

theorem address_width_le (F N L d C b parameter input events : ℕ)
    (hN : 1 ≤ N) (hd : d ≤ parameter)
    (hi : input ≤ F * N ^ (d + C) * (L + 1) ^ b)
    (he : events ≤ F * N ^ (d + C) * (L + 1) ^ b) :
    (input + events).size ≤ (F.size + parameter + C + b + 4) * N * (L + 1) := by
  let T := F * N ^ (d + C) * (L + 1) ^ b
  have hsum : input + events ≤ 2 * T := by dsimp [T]; omega
  have hwidth : (input + events).size ≤
      F.size + (d + C) * N.size + b * (L + 1).size + 4 := by
    calc
      _ ≤ (2 * T).size := Nat.size_le_size hsum
      _ ≤ (2 : ℕ).size + T.size := size_mul_le _ _
      _ ≤ 2 + ((F.size + (N ^ (d + C)).size) + ((L + 1) ^ b).size) := by
        have ht := size_mul_le (F * N ^ (d + C)) ((L + 1) ^ b)
        have hf := size_mul_le F (N ^ (d + C))
        change 2 + T.size ≤ _
        dsimp [T] at *
        omega
      _ ≤ _ := by
        have hn := size_pow_le N (d + C)
        have hl := size_pow_le (L + 1) b
        omega
  have hn := size_le_self N
  have hl := size_le_self (L + 1)
  have hdn := Nat.mul_le_mul (Nat.add_le_add_right hd C) hn
  have hbl := Nat.mul_le_mul_left b hl
  have hx : 1 ≤ N * (L + 1) := Nat.mul_pos (by omega) (by omega)
  have hn' : N ≤ N * (L + 1) := by nlinarith
  have hl' : L + 1 ≤ N * (L + 1) := by nlinarith
  have h1 := Nat.mul_le_mul_left (F.size + 4) hx
  have h2 := Nat.mul_le_mul_left (parameter + C) hn'
  have h3 := Nat.mul_le_mul_left b hl'
  nlinarith

theorem logarithmic_overhead (F N L d C b parameter input events : ℕ)
    (hN : 1 ≤ N) (hd : d ≤ parameter)
    (hi : input ≤ F * N ^ (d + C) * (L + 1) ^ b)
    (he : events ≤ F * N ^ (d + C) * (L + 1) ^ b) :
    events * (102 + 35 * (input + events).size) ≤
      (F * (102 + 35 * (F.size + parameter + C + b + 4))) *
        N ^ (d + (C + 1)) * (L + 1) ^ (b + 1) := by
  have hw := address_width_le F N L d C b parameter input events hN hd hi he
  have hx : 1 ≤ N * (L + 1) := Nat.mul_pos (by omega) (by omega)
  have overhead : 102 + 35 * (input + events).size ≤
      (102 + 35 * (F.size + parameter + C + b + 4)) * N * (L + 1) := by
    nlinarith
  calc
    _ ≤ (F * N ^ (d + C) * (L + 1) ^ b) *
        ((102 + 35 * (F.size + parameter + C + b + 4)) * N * (L + 1)) :=
      Nat.mul_le_mul he overhead
    _ = _ := by rw [show d + (C + 1) = (d + C) + 1 by omega, pow_succ, pow_succ]; ring

end WeightedMIS.RuntimeAbsorption
