import Ski.BitArith
import Ski.Compile
import Nock.Basic

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO pairO ttO ffO val wnf run)

/-!
# Nouns as the Scott sum

Milestone M1 of `PLAN.md`, §2.1: the encoding of nouns that `nock.ski`
(skinock's runtime, in SKIjack) computes over.

    bit  === T | F
    bits === Nil | Cons bit bits
    noun === Atom bits | Cell noun noun | Form noun noun noun | Err

A bit is a Scott Boolean (`bitT`: `T = K`, `F = K I`, lean-ski's `boolT`),
an atom's bits a Scott list least significant first (`bitsT`, lean-ski's
`bl` over `nilT = K` and `consT h t = K (pair h t)`, SKIjack's `nil`/`cons`),
and a noun a four-constructor Scott sum in declaration order:

    Atom b     = λ a c f e. a b
    Cell h t   = λ a c f e. c h t
    Form h t k = λ a c f e. f h t k
    Err        = λ a c f e. e

`atomT`, `cellT`, `formT` and `errT` are those values **as bracket
abstraction gives them** (`absN`, the `_abs` theorems), which is the weak
normal form that skijack's constructor terms `Atom`, `Cell`, `Form`, `Err`
(`AtomC`, …, `ctorO` of `Ski/Compile.lean`) reach when applied to their
fields (`AtomC_red`, …).  `encNoun` encodes lean-nock's `Noun`, an atom's
bits canonical (`bits`: no trailing `false`), so that structural equality
of bit lists is equality of atoms (`bits_inj`) and `inc` on bits is `+1`
(`incB_bits`).  `Form` and `Err` have no `Noun`: `Form` is a cell carrying
compiled code (the compiler's, M2) and `Err` is the crash outcome.

The eliminators (`atomT_elim`, `encNoun_atom_elim`, …) are β for bracket
abstraction, `absN_beta_close`, as `Ski/Requote.lean` proves `quoteS_elim`.
The `_red` lemmas and everything in `Nock2Ski/Prims.lean` are symbolic
runs of open terms checked by the kernel (`BitArith.wnf`, `run`).
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Bits
-- ---------------------------------------------------------------------------

/-- A bit, `T | F`: `K` and `K ⬝ I`. -/
abbrev bitT : Bool → Term := boolT

/-- Bits least significant first, `Nil | Cons bit bits`: `nilT = K`,
    `consT h t = K ⬝ pairT h t`. -/
abbrev bitsT : List Bool → Term := bl

/-- The canonical bits of a number, least significant first, no trailing
    `false`. -/
def bits : Nat → List Bool
  | 0 => []
  | n + 1 => ((n + 1) % 2 == 1) :: bits ((n + 1) / 2)

theorem bits_pos {n : Nat} (h : 0 < n) : bits n = (n % 2 == 1) :: bits (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [bits]

theorem val_bits : ∀ n, val (bits n) = n
  | 0 => by simp [bits, val]
  | n + 1 => by
    rw [bits, val, val_bits ((n + 1) / 2)]
    by_cases h : (n + 1) % 2 = 1
    · simp [h]; omega
    · have h0 : (n + 1) % 2 = 0 := by omega
      simp [h0]; omega
  termination_by n => n
  decreasing_by omega

/-- Bits are canonical, so equal bits are equal numbers. -/
theorem bits_inj {m n : Nat} (h : bits m = bits n) : m = n := by
  have hm := val_bits m
  rw [h, val_bits] at hm
  exact hm.symm

theorem bits_eq_iff (m n : Nat) : bits m = bits n ↔ m = n :=
  ⟨bits_inj, fun h => h ▸ rfl⟩

/-- A number at least `2` has at least two bits. -/
theorem bits_two {n : Nat} (h : 2 ≤ n) : ∃ b c r, bits n = b :: c :: r := by
  rw [bits_pos (by omega), bits_pos (by omega : 0 < n / 2)]
  exact ⟨_, _, _, rfl⟩

/-- `incbk`'s arithmetic: increment a bit list, least significant first. -/
def incB : List Bool → List Bool
  | [] => [true]
  | true :: r => false :: incB r
  | false :: r => true :: r

/-- Incrementing canonical bits is `+ 1` on numbers. -/
theorem incB_bits : ∀ n, incB (bits n) = bits (n + 1)
  | 0 => by simp [bits, incB]
  | n + 1 => by
    rw [bits_pos (by omega : 0 < n + 1), bits_pos (by omega : 0 < n + 1 + 1)]
    by_cases h : (n + 1) % 2 = 1
    · have e : ((n + 1) % 2 == 1) = true := by simp [h]
      have e2 : ((n + 1 + 1) % 2 == 1) = false := by simp; omega
      have e3 : (n + 1) / 2 + 1 = (n + 1 + 1) / 2 := by omega
      rw [e, incB, incB_bits ((n + 1) / 2), e2, e3]
    · have e : ((n + 1) % 2 == 1) = false := by simp [h]
      have e2 : ((n + 1 + 1) % 2 == 1) = true := by simp; omega
      have e3 : (n + 1) / 2 = (n + 1 + 1) / 2 := by omega
      rw [e, incB, e2, e3]
  termination_by n => n
  decreasing_by omega

-- ---------------------------------------------------------------------------
-- The constructors, as skijack compiles them
-- ---------------------------------------------------------------------------

/-- `T`: `λ t f. t`. -/
def TC : Term := toTerm (ctorO 0 0 2)
/-- `F`: `λ t f. f`. -/
def FC : Term := toTerm (ctorO 0 1 2)
/-- `Nil`: `λ n c. n`. -/
def NilC : Term := toTerm (ctorO 0 0 2)
/-- `Cons`: `λ h t n c. c h t`. -/
def ConsC : Term := toTerm (ctorO 2 1 2)
/-- `Atom`: `λ b a c f e. a b`. -/
def AtomC : Term := toTerm (ctorO 1 0 4)
/-- `Cell`: `λ h t a c f e. c h t`. -/
def CellC : Term := toTerm (ctorO 2 1 4)
/-- `Form`: `λ h t k a c f e. f h t k`. -/
def FormC : Term := toTerm (ctorO 3 2 4)
/-- `Err`: `λ a c f e. e`. -/
def ErrC : Term := toTerm (ctorO 0 3 4)

theorem TC_eq : TC = K := rfl
theorem FC_eq : FC = K ⬝ I := rfl
theorem NilC_eq : NilC = nilT := rfl

-- ---------------------------------------------------------------------------
-- Values: the constructors applied to their fields, in weak normal form
-- ---------------------------------------------------------------------------

/-- `Atom b = λ a c f e. a b`, as bracket abstraction gives it. -/
def atomT (b : Term) : Term :=
  S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ b))))

/-- `Cell h t = λ a c f e. c h t`. -/
def cellT (h t : Term) : Term :=
  K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ Compose.pairT h t))

/-- `Form h t k = λ a c f e. f h t k`. -/
def formT (h t k : Term) : Term :=
  K ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ Compose.pairT h t ⬝ (K ⬝ k))))

/-- `Err = λ a c f e. e`, the crash. -/
def errT : Term := K ⬝ (K ⬝ (K ⬝ I))

theorem atomT_abs (b : Term) :
    atomT b = (absN [1, 2, 3, 4] (.var 1 ⬝ₒ .var 0)).close (fun _ => b) := rfl

theorem cellT_abs (h t : Term) :
    cellT h t = (absN [2, 3, 4, 5] (.var 3 ⬝ₒ .var 0 ⬝ₒ .var 1)).close
      (fun i => if i = 0 then h else t) := rfl

theorem formT_abs (h t k : Term) :
    formT h t k = (absN [3, 4, 5, 6] (.var 5 ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2)).close
      (fun i => if i = 0 then h else if i = 1 then t else k) := rfl

theorem errT_abs : errT = (absN [0, 1, 2, 3] (.var 3)).close (fun _ => K) := rfl

theorem errT_eq : errT = ErrC := rfl

/-- **Elimination**: a value selects its continuation and hands it the
    fields, by β for bracket abstraction. -/
theorem atomT_elim (b a c f e : Term) : WSteps (atomT b ⬝ a ⬝ c ⬝ f ⬝ e) (a ⬝ b) := by
  rw [atomT_abs]
  exact absN_beta_close [1, 2, 3, 4] _ (fun _ => b) [a, c, f, e] rfl

theorem cellT_elim (h t a c f e : Term) : WSteps (cellT h t ⬝ a ⬝ c ⬝ f ⬝ e) (c ⬝ h ⬝ t) := by
  rw [cellT_abs]
  exact absN_beta_close [2, 3, 4, 5] _ (fun i => if i = 0 then h else t) [a, c, f, e] rfl

theorem formT_elim (h t k a c f e : Term) :
    WSteps (formT h t k ⬝ a ⬝ c ⬝ f ⬝ e) (f ⬝ h ⬝ t ⬝ k) := by
  rw [formT_abs]
  exact absN_beta_close [3, 4, 5, 6] _ (fun i => if i = 0 then h else if i = 1 then t else k)
    [a, c, f, e] rfl

theorem errT_elim (a c f e : Term) : WSteps (errT ⬝ a ⬝ c ⬝ f ⬝ e) e := by
  rw [errT_abs]
  exact absN_beta_close [0, 1, 2, 3] _ (fun _ => K) [a, c, f, e] rfl

-- ---------------------------------------------------------------------------
-- The same values over open terms, for symbolic runs
-- ---------------------------------------------------------------------------

def atomO (b : OTerm) : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ b))))

def cellO (h t : OTerm) : OTerm :=
  .K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ pairO h t))

def formO (h t k : OTerm) : OTerm :=
  .K ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ pairO h t ⬝ₒ (.K ⬝ₒ k))))

def errO : OTerm := .K ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))

theorem close_atomO (σ : Nat → Term) (b : OTerm) : (atomO b).close σ = atomT (b.close σ) := rfl
theorem close_cellO (σ : Nat → Term) (h t : OTerm) :
    (cellO h t).close σ = cellT (h.close σ) (t.close σ) := rfl
theorem close_formO (σ : Nat → Term) (h t k : OTerm) :
    (formO h t k).close σ = formT (h.close σ) (t.close σ) (k.close σ) := rfl
theorem close_errO (σ : Nat → Term) : errO.close σ = errT := rfl
theorem close_ttO (σ : Nat → Term) : ttO.close σ = boolT true := rfl
theorem close_ffO (σ : Nat → Term) : ffO.close σ = boolT false := rfl

/-- The constructor terms reach the values: `Atom ⬝ b ↠ atomT b`, and so on. -/
theorem AtomC_run : wnf 40 (AtomC.toO ⬝ₒ .var 0) = atomO (.var 0) := by decide +kernel
theorem CellC_run : wnf 40 (CellC.toO ⬝ₒ .var 0 ⬝ₒ .var 1) = cellO (.var 0) (.var 1) := by
  decide +kernel
theorem FormC_run : wnf 40 (FormC.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) =
    formO (.var 0) (.var 1) (.var 2) := by decide +kernel
theorem ConsC_run : wnf 40 (ConsC.toO ⬝ₒ .var 0 ⬝ₒ .var 1) = consO (.var 0) (.var 1) := by
  decide +kernel

theorem AtomC_red (b : Term) : WSteps (AtomC ⬝ b) (atomT b) := by
  have h := run AtomC_run (fun _ => b)
  simp only [OTerm.close, close_toO, close_atomO] at h
  exact h

theorem CellC_red (h t : Term) : WSteps (CellC ⬝ h ⬝ t) (cellT h t) := by
  have e := run CellC_run (fun i => if i = 0 then h else t)
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem FormC_red (h t k : Term) : WSteps (FormC ⬝ h ⬝ t ⬝ k) (formT h t k) := by
  have e := run FormC_run (fun i => if i = 0 then h else if i = 1 then t else k)
  simp only [OTerm.close, close_toO, close_formO] at e
  exact e

theorem ConsC_red (h t : Term) : WSteps (ConsC ⬝ h ⬝ t) (consT h t) := by
  have e := run ConsC_run (fun i => if i = 0 then h else t)
  simp only [OTerm.close, close_toO, BitArith.close_consO] at e
  exact e

-- ---------------------------------------------------------------------------
-- Nouns
-- ---------------------------------------------------------------------------

/-- **The encoding** of a noun: an atom's canonical bits under `Atom`, a
    cell's halves under `Cell`. -/
def encNoun : Noun → Term
  | .atom n => atomT (bitsT (bits n))
  | .cell h t => cellT (encNoun h) (encNoun t)

theorem encNoun_atom (n : Nat) : encNoun (.atom n) = atomT (bitsT (bits n)) := rfl
theorem encNoun_cell (h t : Noun) : encNoun (.cell h t) = cellT (encNoun h) (encNoun t) := rfl

/-- `⟨n⟩ a c f e ↠ a ⟨bits n⟩`. -/
theorem encNoun_atom_elim (n : Nat) (a c f e : Term) :
    WSteps (encNoun (.atom n) ⬝ a ⬝ c ⬝ f ⬝ e) (a ⬝ bitsT (bits n)) :=
  atomT_elim ..

/-- `⟨[h t]⟩ a c f e ↠ c ⟨h⟩ ⟨t⟩`. -/
theorem encNoun_cell_elim (h t : Noun) (a c f e : Term) :
    WSteps (encNoun (.cell h t) ⬝ a ⬝ c ⬝ f ⬝ e) (c ⬝ encNoun h ⬝ encNoun t) :=
  cellT_elim ..

end Nock2Ski
