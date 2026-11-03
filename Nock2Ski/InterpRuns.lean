import Nock2Ski.InterpPinsE

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# decop: an opcode's bits to its tag

Kernel runs of `decop` (`BitArith.wnf`, `run`) on the canonical bits of
`0 … 15` and on any five bits or more: `decop_spec` reads `bits k` to the
tag `O_k` for `k ≤ 12` and to `Obad` from 13 on.  `bits_1 … bits_15` and
`bits_five` are the bit patterns.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Scott lists
-- ---------------------------------------------------------------------------

theorem nilT_elim (n c : Term) : WSteps (nilT ⬝ n ⬝ c) n := .single (.K _ _)

theorem consT_elim (h t n c : Term) : WSteps (consT h t ⬝ n ⬝ c) (c ⬝ h ⬝ t) :=
  .step (.left _ (.K _ _)) (Compose.pairT_app h t c)

theorem bitsT_nil : bitsT [] = nilT := rfl
theorem bitsT_cons (b : Bool) (bs : List Bool) : bitsT (b :: bs) = consT (boolT b) (bitsT bs) := rfl

-- ---------------------------------------------------------------------------
-- decop: an opcode's bits to its tag
-- ---------------------------------------------------------------------------

/-- The canonical bits of `0 … 15`. -/
theorem bits_1 : bits 1 = [true] := bits_one
theorem bits_2 : bits 2 = [false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_3 : bits 3 = [true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_4 : bits 4 = [false, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_5 : bits 5 = [true, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_6 : bits 6 = [false, true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_7 : bits 7 = [true, true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_8 : bits 8 = [false, false, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_9 : bits 9 = [true, false, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_10 : bits 10 = [false, true, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_11 : bits 11 = [true, true, false, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_12 : bits 12 = [false, false, true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_13 : bits 13 = [true, false, true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_14 : bits 14 = [false, true, true, true] := by simp (disch := omega) [bits_pos, bits_zero]
theorem bits_15 : bits 15 = [true, true, true, true] := by simp (disch := omega) [bits_pos, bits_zero]

/-- A number at least `16` has at least five bits. -/
theorem bits_five {k : Nat} (h : 16 ≤ k) :
    ∃ b0 b1 b2 b3 b4 r, bits k = b0 :: b1 :: b2 :: b3 :: b4 :: r := by
  rw [bits_pos (by omega), bits_pos (by omega : 0 < k / 2), bits_pos (by omega : 0 < k / 2 / 2),
    bits_pos (by omega : 0 < k / 2 / 2 / 2), bits_pos (by omega : 0 < k / 2 / 2 / 2 / 2)]
  exact ⟨_, _, _, _, _, _, rfl⟩

/-- A symbolic run of `decop` on explicit bits, closed. -/
theorem decop_of_run {L : List Bool} {j : Nat}
    (h : wnf 300 (decopT.toO ⬝ₒ (bitsT L).toO) = (opC j).toO) : WSteps (decopT ⬝ bitsT L) (opC j) := by
  have e := run h (fun _ => K)
  rwa [close_app, close_toO, close_toO, close_toO] at e

theorem decop_run0 : wnf 300 (decopT.toO ⬝ₒ (bitsT []).toO) = (opC 0).toO := by decide +kernel
theorem decop_run1 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true]).toO) = (opC 1).toO := by decide +kernel
theorem decop_run2 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, true]).toO) = (opC 2).toO := by decide +kernel
theorem decop_run3 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, true]).toO) = (opC 3).toO := by decide +kernel
theorem decop_run4 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, false, true]).toO) = (opC 4).toO := by decide +kernel
theorem decop_run5 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, false, true]).toO) = (opC 5).toO := by decide +kernel
theorem decop_run6 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, true, true]).toO) = (opC 6).toO := by decide +kernel
theorem decop_run7 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, true, true]).toO) = (opC 7).toO := by decide +kernel
theorem decop_run8 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, false, false, true]).toO) = (opC 8).toO := by decide +kernel
theorem decop_run9 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, false, false, true]).toO) = (opC 9).toO := by decide +kernel
theorem decop_run10 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, true, false, true]).toO) = (opC 10).toO := by decide +kernel
theorem decop_run11 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, true, false, true]).toO) = (opC 11).toO := by decide +kernel
theorem decop_run12 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, false, true, true]).toO) = (opC 12).toO := by decide +kernel
theorem decop_run13 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, false, true, true]).toO) = (opC 13).toO := by decide +kernel
theorem decop_run14 : wnf 300 (decopT.toO ⬝ₒ (bitsT [false, true, true, true]).toO) = (opC 13).toO := by decide +kernel
theorem decop_run15 : wnf 300 (decopT.toO ⬝ₒ (bitsT [true, true, true, true]).toO) = (opC 13).toO := by decide +kernel

/-- Five bits or more: `Obad`, whatever they are. -/
theorem decop_run_bad : ∀ b0 b1 b2 b3 : Bool,
    wnf 400 (decopT.toO ⬝ₒ consO (boolT b0).toO (consO (boolT b1).toO (consO (boolT b2).toO
      (consO (boolT b3).toO (consO (.var 10) (.var 11)))))) = (opC 13).toO := by
  decide +kernel

/-- **`decop`** reads canonical bits to the opcode's tag, `Obad` from 13 on. -/
theorem decop_spec (k : Nat) : WSteps (decopT ⬝ bitsT (bits k)) (opC (if k ≤ 12 then k else 13)) := by
  match k with
  | 0 => rw [bits_zero]; exact decop_of_run decop_run0
  | 1 => rw [bits_1]; exact decop_of_run decop_run1
  | 2 => rw [bits_2]; exact decop_of_run decop_run2
  | 3 => rw [bits_3]; exact decop_of_run decop_run3
  | 4 => rw [bits_4]; exact decop_of_run decop_run4
  | 5 => rw [bits_5]; exact decop_of_run decop_run5
  | 6 => rw [bits_6]; exact decop_of_run decop_run6
  | 7 => rw [bits_7]; exact decop_of_run decop_run7
  | 8 => rw [bits_8]; exact decop_of_run decop_run8
  | 9 => rw [bits_9]; exact decop_of_run decop_run9
  | 10 => rw [bits_10]; exact decop_of_run decop_run10
  | 11 => rw [bits_11]; exact decop_of_run decop_run11
  | 12 => rw [bits_12]; exact decop_of_run decop_run12
  | 13 => rw [bits_13]; exact decop_of_run decop_run13
  | 14 => rw [bits_14]; exact decop_of_run decop_run14
  | 15 => rw [bits_15]; exact decop_of_run decop_run15
  | k + 16 =>
    obtain ⟨b0, b1, b2, b3, b4, r, hb⟩ := bits_five (k := k + 16) (by omega)
    rw [hb, if_neg (by omega)]
    have e := run (decop_run_bad b0 b1 b2 b3) (fun i => if i = 10 then boolT b4 else bitsT r)
    simp only [close_app, close_toO, BitArith.close_consO, close_var, ↓reduceIte, Nat.reduceEqDiff] at e
    exact e

theorem decop_le {k : Nat} (h : k ≤ 12) : WSteps (decopT ⬝ bitsT (bits k)) (opC k) := by
  have e := decop_spec k; rwa [if_pos h] at e
theorem decop_bad {k : Nat} (h : 13 ≤ k) : WSteps (decopT ⬝ bitsT (bits k)) (opC 13) := by
  have e := decop_spec k; rwa [if_neg (by omega)] at e


end Nock2Ski
