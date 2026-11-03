module

public import HadamardMultibase.GolayOperations

@[expose] public section

namespace HadamardMultibase

open scoped LaurentPolynomial

def plusPart {m : ℕ} (A B : Fin m → ℤ) : Fin m → ℤ :=
  fun i => if A i = B i then A i else 0

def minusPart {m : ℕ} (A B : Fin m → ℤ) : Fin m → ℤ :=
  fun i => if A i = B i then 0 else A i

theorem binary_parts_add {m : ℕ} {A B : Fin m → ℤ} (hA : IsBinary A) (hB : IsBinary B) :
    A = plusPart A B + minusPart A B := by
  ext i
  obtain ha | ha := hA i <;> obtain hb | hb := hB i <;>
    simp [plusPart, minusPart, ha, hb]

theorem binary_parts_sub {m : ℕ} {A B : Fin m → ℤ} (hA : IsBinary A) (hB : IsBinary B) :
    B = plusPart A B - minusPart A B := by
  ext i
  obtain ha | ha := hA i <;> obtain hb | hb := hB i <;>
    simp [plusPart, minusPart, ha, hb]

def turynA {m n : ℕ} (A B : Fin m → ℤ) (C D : Fin n → ℤ) : Fin (n * m) → ℤ :=
  tensorSequence (plusPart A B) C + tensorSequence (minusPart A B) (reverseSequence D)

def turynB {m n : ℕ} (A B : Fin m → ℤ) (C D : Fin n → ℤ) : Fin (n * m) → ℤ :=
  tensorSequence (plusPart A B) D - tensorSequence (minusPart A B) (reverseSequence C)

theorem turynA_binary {m n : ℕ} {A B : Fin m → ℤ} {C D : Fin n → ℤ}
    (hA : IsBinary A) (hC : IsBinary C) (hD : IsBinary D) :
    IsBinary (turynA A B C D) := by
  intro k
  let i := (finProdFinEquiv.symm k).2
  let j := (finProdFinEquiv.symm k).1
  change plusPart A B i * C j + minusPart A B i * D j.rev = 1 ∨
    plusPart A B i * C j + minusPart A B i * D j.rev = -1
  by_cases hi : A i = B i
  · simp only [plusPart, minusPart, ite_eq_left hi, zero_mul, add_zero]
    obtain ha | ha := hA i <;> obtain hc | hc := hC j <;> simp [ha, hc]
  · simp only [plusPart, minusPart, ite_eq_right hi, zero_mul, zero_add]
    obtain ha | ha := hA i <;> obtain hd | hd := hD j.rev <;> simp [ha, hd]

theorem turynB_binary {m n : ℕ} {A B : Fin m → ℤ} {C D : Fin n → ℤ}
    (hA : IsBinary A) (hC : IsBinary C) (hD : IsBinary D) :
    IsBinary (turynB A B C D) := by
  intro k
  let i := (finProdFinEquiv.symm k).2
  let j := (finProdFinEquiv.symm k).1
  change plusPart A B i * D j - minusPart A B i * C j.rev = 1 ∨
    plusPart A B i * D j - minusPart A B i * C j.rev = -1
  by_cases hi : A i = B i
  · simp only [plusPart, minusPart, ite_eq_left hi, zero_mul, sub_zero]
    obtain ha | ha := hA i <;> obtain hd | hd := hD j <;> simp [ha, hd]
  · simp only [plusPart, minusPart, ite_eq_right hi, zero_mul, zero_sub]
    obtain ha | ha := hA i <;> obtain hc | hc := hC j.rev <;> simp [ha, hc]

theorem IsGolayPair.turyn {m n : ℕ} {A B : Fin m → ℤ} {C D : Fin n → ℤ}
    (hAB : IsGolayPair A B) (hCD : IsGolayPair C D) :
    IsGolayPair (turynA A B C D) (turynB A B C D) := by
  apply isGolayPair_of_laurentEnergy
    (turynA_binary hAB.1 hCD.1 hCD.2.1) (turynB_binary hAB.1 hCD.1 hCD.2.1)
  have ha : sequenceLaurent A =
      sequenceLaurent (plusPart A B) + sequenceLaurent (minusPart A B) := by
    rw [← sequenceLaurent_add]
    exact congrArg sequenceLaurent (binary_parts_add hAB.1 hAB.2.1)
  have hb : sequenceLaurent B =
      sequenceLaurent (plusPart A B) - sequenceLaurent (minusPart A B) := by
    rw [← sequenceLaurent_sub]
    exact congrArg sequenceLaurent (binary_parts_sub hAB.1 hAB.2.1)
  have hparts : 2 * (laurentEnergy (sequenceLaurent (plusPart A B)) +
      laurentEnergy (sequenceLaurent (minusPart A B))) = LaurentPolynomial.C (2 * m : ℚ) := by
    rw [← hAB.laurentEnergy_eq, ha, hb]
    simp only [laurentEnergy, map_add, map_sub]
    ring
  have hcd : laurentEnergy (laurentDilate m (sequenceLaurent C)) +
      laurentEnergy (laurentDilate m (sequenceLaurent D)) = LaurentPolynomial.C (2 * n : ℚ) := by
    rw [laurentEnergy_dilate, laurentEnergy_dilate, ← map_add, hCD.laurentEnergy_eq,
      laurentDilate_C]
  dsimp only [turynA, turynB]
  rw [sequenceLaurent_add, sequenceLaurent_sub]
  simp only [sequenceLaurent_tensor, sequenceLaurent_reverse, map_mul,
    laurentDilate_invert, laurentDilate_T, ← mul_assoc]
  rw [laurent_turyn_parts_identity, hcd]
  calc
    _ = (2 * (laurentEnergy (sequenceLaurent (plusPart A B)) +
        laurentEnergy (sequenceLaurent (minusPart A B)))) * LaurentPolynomial.C (n : ℚ) := by
      simp only [map_mul, map_ofNat]
      ring
    _ = _ := by
      rw [hparts]
      simp only [← map_mul]
      apply congrArg LaurentPolynomial.C
      push_cast
      ring

theorem GolayLength.mul {m n : ℕ} (hm : GolayLength m) (hn : GolayLength n) :
    GolayLength (m * n) := by
  obtain ⟨hm, A, B, hAB⟩ := hm
  obtain ⟨hn, C, D, hCD⟩ := hn
  have h : GolayLength (n * m) :=
    ⟨Nat.mul_pos hn hm, turynA A B C D, turynB A B C D, hAB.turyn hCD⟩
  simpa [mul_comm] using h

theorem GolayLength.pow {m : ℕ} (hm : GolayLength m) (a : ℕ) : GolayLength (m ^ a) := by
  induction a with
  | zero => simpa using golayLength_one
  | succ a ih => simpa [pow_succ] using ih.mul hm

theorem golayFamily : GolayFamily := fun a b =>
  (golayLength_two.pow a).mul (golayLength_ten.pow b)

theorem golayLength_monoid₃ (a b c : ℕ) : GolayLength (2 ^ a * 10 ^ b * 26 ^ c) :=
  ((golayLength_two.pow a).mul (golayLength_ten.pow b)).mul (golayLength_twentySix.pow c)

end HadamardMultibase
