import Nock2Ski.Interp
import Nock.Eval

open Term

/-!
# The compiler: Nock formulas to closed SKI terms

Milestone M2 of `PLAN.md`, §2.2–2.3: `nockToSki : Noun → Term`, the Lean
twin of `python/skinock/compile.py`'s `Compiler.formula`.  A formula `f`
compiles to a closed term `nockToSki f` that takes the encoded subject as
its one argument; `nockToSki f ⬝ s` is Python's `formula(f, "s")`.

## Mirroring `compile.py`

Each opcode is one combinator of the runtime (`Nock2Ski/Prims.lean`)
applied to the compiled operands, with `force` wherever Nock evaluates an
operand before using it, in lean-nock's order:

| formula | `nockToSki` applied to `s` |
|---|---|
| `[[b c] d]` | `force (B s) (consK (D s))`, `consK e x = force e (Cell x)` |
| `[0 n]`, `n ≥ 1` | the `hd`/`tl` chain of `n`'s binary digits (`axisO`) |
| `[0 0]`, `[0 [..]]` | `Err` |
| `[1 r]` | `encLit r` (`K ⬝ encLit r` before the subject) |
| `[2 b c]` | `force (B s) (appK (C s))`, `appK e x = force e (λg. app g x)` |
| `[3 b]`, `[4 b]` | `cel (B s)`, `inc (B s)` |
| `[5 b c]` | `force (B s) (eqK (C s))`, `eqK e x = force e (eq x)` |
| `[6 b c d]` | `ifn (B s) (C s) (D s)`: the branches stay unevaluated |
| `[7 b c]` | `force (B s) C` |
| `[8 b c]` | `force (B s) (pushK C s)`, `pushK c s x = c (Cell x s)` |
| `[9 n c]` | `force (C s) (pullK n)`, `pullK n core = app (axis n core) core` |
| `[10 [n c] d]` | `force (D s) (editK n (C s))`, `editK n c t = force c (λv. editAx n v t)` |
| `[11 t c]` | `C` |
| `[11 [t h] c]` | `force (H s) (K (C s))` |
| anything else | `Err` |

The λs `compile.py` writes (`force X (\x. …)`) are bracket abstraction,
`absN`, over open terms whose globals are the closed terms above; every
compiled subformula is itself closed, so a node's binders are the fixed
variables `0`, `1`, `2`, …, and β is `absN_beta_close`.  Python's
`(\x. formula(c, x))` is `C` by η, and its `(\s2. …) (Cell x s)` is
`C (Cell x s)`.  `compile.py` hash-conses literals and formula bodies into
named definitions, a size optimisation the Lean side does not need.

**One deliberate difference.**  `compile.py` forces opcode 10's patch `c`
before its tree `d`; lean-nock's `NockEval.op10` (and Vere, `Nock/Order.lean`)
evaluate the tree `d` first.  The simulation (`Nock2Ski/Embed.lean`) is
stated against lean-nock, so `nockToSki` takes lean-nock's order.  The two
differ only when one operand crashes and the other diverges.

## Literals

`encLit` is `compile.py`'s `lit`: an atom's bits under `Atom`, a cell under
`Cell`, except that a cell that parses as a formula (`isFormula`, nock.py's
`is_formula`) is a `Form` carrying its own compiled code, so a battery
pushed by `[1 …]` has live arms for opcode 9 (`app_form`).  `encLit` and
`nockToSki` are mutually recursive (a literal formula's code compiles the
literal) and defined by well-founded recursion on the noun's size.

## Axes

`axisPath n` is the list of binary digits of `n ≥ 1` below its leading one,
`false` for the head and `true` for the tail, and equals `Front.axisSteps`
(`axisPath_eq_axisSteps`); it is defined by recursion on `n` so that Nock's
`fasO` and `haxO` can be related to the path (`Nock2Ski/Embed.lean`).
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Shapes: nock.py's `is_formula` and `malformed`
-- ---------------------------------------------------------------------------

/-- Does the noun parse as a Nock 4K formula?  nock.py's `is_formula`:
    an autocons needs both halves formulas; `[0 b]` needs an atom axis;
    `[1 b]` always; the operand counts of 2–12 as the spec gives them, a
    dynamic hint `[11 [t h] c]` with an atom tag. -/
def isFormula : Noun → Bool
  | .atom _ => false
  | .cell (.cell a b) r => isFormula (.cell a b) && isFormula r
  | .cell (.atom 0) (.atom _) => true
  | .cell (.atom 0) (.cell _ _) => false
  | .cell (.atom 1) _ => true
  | .cell (.atom 2) (.cell a b) => isFormula a && isFormula b
  | .cell (.atom 3) r => isFormula r
  | .cell (.atom 4) r => isFormula r
  | .cell (.atom 5) (.cell a b) => isFormula a && isFormula b
  | .cell (.atom 6) (.cell a (.cell b c)) => isFormula a && isFormula b && isFormula c
  | .cell (.atom 7) (.cell a b) => isFormula a && isFormula b
  | .cell (.atom 8) (.cell a b) => isFormula a && isFormula b
  | .cell (.atom 9) (.cell (.atom _) b) => isFormula b
  | .cell (.atom 10) (.cell (.cell (.atom _) a) b) => isFormula a && isFormula b
  | .cell (.atom 11) (.cell (.cell (.atom _) a) b) => isFormula a && isFormula b
  | .cell (.atom 11) (.cell (.atom _) b) => isFormula b
  | .cell (.atom 12) (.cell a b) => isFormula a && isFormula b
  | _ => false

/-- The shallow shape check a node makes before its operands run, as
    nock.py's `malformed` groups the opcodes. -/
def malformed : Noun → Bool
  | .atom _ => true
  | .cell (.cell _ _) _ => false
  | .cell (.atom op) t =>
    if op = 0 ∨ op = 1 ∨ op = 3 ∨ op = 4 then false
    else if op = 2 ∨ op = 5 ∨ op = 7 ∨ op = 8 ∨ op = 9 ∨ op = 11 then
      match t with | .cell _ _ => false | .atom _ => true
    else if op = 6 then
      match t with | .cell _ (.cell _ _) => false | _ => true
    else if op = 10 then
      match t with | .cell (.cell _ _) _ => false | _ => true
    else true

/-- `malformed` is lean-nock's `Malformed`. -/
theorem malformed_eq : malformed = Malformed := by
  funext f
  cases f with
  | atom _ => rfl
  | cell h t =>
    cases h with
    | cell _ _ => rfl
    | atom op =>
      match op with
      | 0 | 1 | 3 | 4 => cases t <;> rfl
      | 2 | 5 | 7 | 8 | 9 | 11 => cases t <;> rfl
      | 6 => cases t with
        | atom _ => rfl
        | cell _ r => cases r <;> rfl
      | 10 => cases t with
        | atom _ => rfl
        | cell l _ => cases l <;> rfl
      | n + 12 => cases t <;> rfl

-- ---------------------------------------------------------------------------
-- Axes (`axisPath` and `axisPath_eq_axisSteps` are in `Interp.lean`)
-- ---------------------------------------------------------------------------

/-- The `hd`/`tl` chain along a path, first step innermost, over open terms
    (`pickT` of `Prims.lean` over `Term`). -/
def pickO (e : OTerm) : List Bool → OTerm
  | [] => e
  | b :: bs => pickO ((if b then tlT else hdT).toO ⬝ₒ e) bs

theorem close_pickO (σ : Nat → Term) : ∀ (bs : List Bool) (e : OTerm),
    (pickO e bs).close σ = pickT (e.close σ) bs
  | [], _ => rfl
  | b :: bs, e => by
    rw [pickO, pickT, close_pickO σ bs]
    cases b <;> rfl

/-- Axis `n` of `e`: the chain of `n`'s digits, or `Err` at axis `0`. -/
def axisO (n : Nat) (e : OTerm) : OTerm :=
  match n with
  | 0 => errT.toO
  | _ + 1 => pickO e (axisPath n)

-- ---------------------------------------------------------------------------
-- The λs of compile.py, as closed combinators
-- ---------------------------------------------------------------------------

local notation "v0" => OTerm.var 0
local notation "v1" => OTerm.var 1
local notation "v2" => OTerm.var 2
local notation "v3" => OTerm.var 3
local notation "v4" => OTerm.var 4

/-- `λ e x. force e (Cell x)`: the second half of an autocons. -/
def consK : Term := toTerm (absN [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ (CellC.toO ⬝ₒ v1)))

/-- `λ e x. force e (λ g. app g x)`: opcode 2's formula, forced, applied to
    the subject `x`. -/
def appK : Term := toTerm (absN [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] (appT.toO ⬝ₒ v2 ⬝ₒ v1)))

/-- `λ e x. force e (eq x)`: opcode 5's second operand. -/
def eqK : Term := toTerm (absN [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ (eqT.toO ⬝ₒ v1)))

/-- `λ c s x. c (Cell x s)`: opcode 8 runs `c` on the pushed subject. -/
def pushK : Term := toTerm (absN [0, 1, 2] (v0 ⬝ₒ (CellC.toO ⬝ₒ v2 ⬝ₒ v1)))

/-- `λ core. app (axis n core) core`: opcode 9 pulls the arm and runs it on
    the core; a cell axis is a crash after the core is forced. -/
def pullK : Noun → Term
  | .atom n => toTerm (absN [0] (appT.toO ⬝ₒ axisO n v0 ⬝ₒ v0))
  | .cell _ _ => K ⬝ errT

/-- `λ v cur. …`: compile.py's `edit` along a path, the rebuilt subtree
    forced before its `Cell` is built so a crash under the path cannot hide
    in a field of the product. -/
def editT : List Bool → Term
  | [] => K
  | false :: bs => toTerm (absN [0, 1]
      (forceT.toO ⬝ₒ (hdT.toO ⬝ₒ v1) ⬝ₒ absN [2]
        (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
          (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4]
            (CellC.toO ⬝ₒ v4 ⬝ₒ v3)))))
  | true :: bs => toTerm (absN [0, 1]
      (forceT.toO ⬝ₒ (hdT.toO ⬝ₒ v1) ⬝ₒ absN [2]
        (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
          (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4]
            (CellC.toO ⬝ₒ v2 ⬝ₒ v4)))))

/-- `λ v t. #[n v t]`: the edit at a static axis; `0` and a cell axis crash. -/
def editAx : Noun → Term
  | .atom 0 => K ⬝ (K ⬝ errT)
  | .atom (n + 1) => editT (axisPath (n + 1))
  | .cell _ _ => K ⬝ (K ⬝ errT)

/-- `λ c t. force c (λ v. editAx n v t)`: opcode 10 after its tree. -/
def editK (n : Noun) : Term :=
  toTerm (absN [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] ((editAx n).toO ⬝ₒ v2 ⬝ₒ v1)))

-- ---------------------------------------------------------------------------
-- The compiler
-- ---------------------------------------------------------------------------

/-- `λ s. body`, the subject the variable `0`. -/
def lamS (body : OTerm) : Term := toTerm (absN [0] body)

/-- The compiled subformula applied to the subject variable. -/
def at0 (c : Term) : OTerm := c.toO ⬝ₒ v0

mutual
/-- **The compiler.**  `nockToSki f ⬝ s` runs the formula `f` on the
    encoded subject `s`, as `compile.py`'s `formula(f, s)`. -/
def nockToSki : Noun → Term
  | .cell (.cell b c) d =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki (.cell b c)) ⬝ₒ (consK.toO ⬝ₒ at0 (nockToSki d)))
  | .cell (.atom 0) (.atom n) => lamS (axisO n v0)
  | .cell (.atom 1) r => K ⬝ encLit r
  | .cell (.atom 2) (.cell b c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki b) ⬝ₒ (appK.toO ⬝ₒ at0 (nockToSki c)))
  | .cell (.atom 3) b => lamS (celT.toO ⬝ₒ at0 (nockToSki b))
  | .cell (.atom 4) b => lamS (incT.toO ⬝ₒ at0 (nockToSki b))
  | .cell (.atom 5) (.cell b c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki b) ⬝ₒ (eqK.toO ⬝ₒ at0 (nockToSki c)))
  | .cell (.atom 6) (.cell b (.cell c d)) =>
    lamS (ifnT.toO ⬝ₒ at0 (nockToSki b) ⬝ₒ at0 (nockToSki c) ⬝ₒ at0 (nockToSki d))
  | .cell (.atom 7) (.cell b c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki b) ⬝ₒ (nockToSki c).toO)
  | .cell (.atom 8) (.cell b c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki b) ⬝ₒ (pushK.toO ⬝ₒ (nockToSki c).toO ⬝ₒ v0))
  | .cell (.atom 9) (.cell b c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki c) ⬝ₒ (pullK b).toO)
  | .cell (.atom 10) (.cell (.cell b c) d) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki d) ⬝ₒ ((editK b).toO ⬝ₒ at0 (nockToSki c)))
  | .cell (.atom 11) (.cell (.atom _) c) => nockToSki c
  | .cell (.atom 11) (.cell (.cell _ h) c) =>
    lamS (forceT.toO ⬝ₒ at0 (nockToSki h) ⬝ₒ (.K ⬝ₒ at0 (nockToSki c)))
  | _ => K ⬝ errT
termination_by f => 2 * sizeOf f
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- **Literals**, `compile.py`'s `lit`: a formula-shaped cell is a `Form`
    carrying its compiled code, any other cell a `Cell`. -/
def encLit : Noun → Term
  | .atom n => atomT (bitsT (bits n))
  | .cell h t =>
    if isFormula (.cell h t) then formT (encLit h) (encLit t) (nockToSki (.cell h t))
    else cellT (encLit h) (encLit t)
termination_by n => 2 * sizeOf n + 1
decreasing_by
  all_goals simp_wf
  all_goals omega
end

/-- A malformed formula (lean-nock's `Malformed`) compiles to the crash. -/
theorem nockToSki_malformed {f : Noun} (h : Malformed f = true) : nockToSki f = K ⬝ errT := by
  cases f with
  | atom _ => rw [nockToSki.eq_def]
  | cell hd t =>
    cases hd with
    | cell _ _ => simp [Malformed] at h
    | atom op =>
      match op, t with
      | 0, .atom _ | 0, .cell _ _ | 1, _ | 3, _ | 4, _ => simp [Malformed] at h
      | 2, .cell _ _ | 5, .cell _ _ | 7, .cell _ _ | 8, .cell _ _ | 9, .cell _ _ | 11, .cell _ _
      | 6, .cell _ (.cell _ _) | 10, .cell (.cell _ _) _ => simp [Malformed] at h
      | 2, .atom _ | 5, .atom _ | 7, .atom _ | 8, .atom _ | 9, .atom _ | 11, .atom _ =>
        rw [nockToSki.eq_def]; rfl
      | 6, .atom _ | 6, .cell _ (.atom _) => rw [nockToSki.eq_def]; rfl
      | 10, .atom _ | 10, .cell (.atom _) _ => rw [nockToSki.eq_def]; rfl
      | _ + 12, _ => rw [nockToSki.eq_def]; rfl

/-- A program on a subject: the compiled formula applied to the subject
    encoded as the runtime encodes its literal, formula-shaped cells with
    their code (`compile.py`'s `subj := lit(subject)`).  `encNoun s`, the
    code-free encoding, is the other admissible subject (`Embed.lean`'s
    `Enc`); it is what a hidden subject must use, since code cannot depend
    on hidden data. -/
def compiled (f s : Noun) : Term := nockToSki f ⬝ encLit s

end Nock2Ski
