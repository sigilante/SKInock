import Nock2Ski.Share

open Term
open Compose (boolT pairT)
open BitArith (nilT consT val)

/-!
# A Nock program over a hidden atom: the predicate statement (M4c)

lean-ski's predicate statement (`Ski/Predicate.lean`) hands its verifier
`V`, a closed term, the public `x` and `k` literal bits `ρ` in the
circuit's layout, `boolsT`: a `pairT` chain of Scott Booleans, the last
bit alone, each cell constrained to `K` or `K I` by the composed circuit.
The statement here is **"I know an atom `n` of `k` bits with `*[n f] =
p`"** for a public formula `f` and product `p`:

    nockPredV f k = share (λ x ρ. eqn (nockToSki f (Atom (toBitsT k ρ))) x)

applied by the circuit to `x = encNoun p` and the bits.  `toBitsT k`
converts the circuit's `k` bits to the runtime's canonical bit list
(`bitsT`, least significant first, no trailing `F`): a right fold of
`consTrimT`, which conses a bit onto a trimmed list and drops a trailing
`F` (`trim`).  So the subject the compiled formula sees is exactly
`encNoun (.atom n)` for `n` the bits' value, and `eqn` (`eqn_enc`) answers
`K` exactly when the product's encoding is `encNoun p`'s.

**Completeness** (`nock_pred_complete`): `NockEval (.atom n) f (.val p)`
with `n < 2^k` makes the verifier accept the `k` bits of `n`, by
`embed_value_encNoun` and `eqn_enc`.

**Soundness** (`nock_pred_sound`): the verifier accepting `encNoun p` on
`k` bits, which is what lean-ski's `Circuit.predExport_sound` concludes of
an accepted proof of the predicate circuit `predAirs V x k W`, shows bits
of value `n < 2^k` with `eqn (nockToSki f ⬝ encNoun (.atom n)) (encNoun p)
↠ K`: the SKI compilation of `f`, on the hidden atom, is `eqn`-equal to
`p`'s encoding.
That is a statement about the SKI term, as every lean-ski statement is
about its term.  Carried to Nock it says: if Nock evaluates `f` on `n` to
any value `q`, then `q = p` (`nock_pred_sound_val`: `embed_value_encNoun`
and Church–Rosser, since `eqn` answers `F` on unequal encodings and `F`
never reaches `K`), and Nock does not crash on `n` (`nock_pred_sound_crash`:
`eqn` answers `F` on `Err`).  What is **not** proved is that Nock
terminates on `n`: the converse simulation (SKI value ⇒ Nock value) needs
fuel adequacy on both sides (`embed_diverges`, PLAN.md M3's open item), so
an accepted proof leaves open that Nock diverges on the hidden atom while
the SKI term, which simulates it, found a value anyway — which the
simulation theorems do not exclude only because they are stated in one
direction.

**The join to the circuit is by hand.**  lean-ski's `Ski.Predicate` and
`Ski.Circuit.CompPred` cannot be imported beside lean-nock: `Ski.Composed`
reaches `Ski.Words` (through `Ski.AirProbe`, `Ski.ProbeTree`,
`Ski.Decode`), whose root-level `inductive Outcome` (`Ski/Words.lean:157`)
clashes with lean-nock's root-level `Outcome` (`Nock/Eval.lean:62`), so
Lean refuses the import (`Outcome.val.inj` defined twice).  `boolsT` below
is therefore a copy of `CompM.boolsT`, character for character, and
`nock_pred_sound`'s hypothesis is the conclusion of `predExport_sound` at
`V = nockPredV f k`, `x = encNoun p`, `n = k`, read across the two
environments; the composition is one `obtain` once either library moves
its `Outcome` into a namespace.
-/

namespace Nock2Ski

/-- lean-ski's `CompM.boolsT` (`Ski/Predicate.lean`): the circuit's `k`
    bits as a term, the last alone, each before it paired with the rest. -/
def boolsT : List Bool → Term
  | [] => boolT false
  | [b] => boolT b
  | b :: r => pairT (boolT b) (boolsT r)

-- ---------------------------------------------------------------------------
-- Fixed-width bits and their canonical form
-- ---------------------------------------------------------------------------

/-- The `k` low bits of `n`, least significant first: the witness. -/
def bitsK : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: bitsK k (n / 2)

theorem bitsK_length : ∀ k n, (bitsK k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [bitsK, bitsK_length k]

theorem val_bitsK : ∀ k n, n < 2 ^ k → val (bitsK k n) = n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rfl
  | k + 1, n, h => by
    have h2 : n / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at h; omega
    rw [bitsK, val, val_bitsK k (n / 2) h2]
    by_cases hp : n % 2 = 1
    · simp [hp]; omega
    · have h0 : n % 2 = 0 := by omega
      simp [h0]; omega

/-- A list's value is below `2^length`. -/
theorem val_lt : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by simp [val]
  | b :: r => by
    have := val_lt r
    rw [val, List.length_cons, Nat.pow_succ]
    cases b <;> simp [Bool.toNat] <;> omega

/-- Cons a bit onto a canonical list, keeping it canonical: a `false` onto
    the empty list is dropped. -/
def consTrim (b : Bool) : List Bool → List Bool
  | [] => if b then [true] else []
  | c :: r => b :: c :: r

/-- Strip the trailing `false`s. -/
def trim : List Bool → List Bool
  | [] => []
  | b :: r => consTrim b (trim r)

/-- No trailing `false`. -/
def canon : List Bool → Bool
  | [] => true
  | [b] => b
  | _ :: c :: r => canon (c :: r)

theorem canon_consTrim (b : Bool) : ∀ l, canon l = true → canon (consTrim b l) = true
  | [], _ => by cases b <;> rfl
  | _ :: _, h => h

theorem canon_trim : ∀ l, canon (trim l) = true
  | [] => rfl
  | b :: r => canon_consTrim b _ (canon_trim r)

theorem val_consTrim (b : Bool) : ∀ l, val (consTrim b l) = b.toNat + 2 * val l
  | [] => by cases b <;> rfl
  | _ :: _ => rfl

theorem val_trim : ∀ l, val (trim l) = val l
  | [] => rfl
  | b :: r => by rw [trim, val_consTrim, val_trim r, val]

theorem val_pos_of_canon : ∀ l, canon l = true → l ≠ [] → 0 < val l
  | [], _, h => absurd rfl h
  | [b], h, _ => by
    have : b = true := h
    subst this; decide
  | b :: c :: r, h, _ => by
    have := val_pos_of_canon (c :: r) h (by simp)
    rw [val]; omega

/-- **Canonical bits are `bits` of their value.** -/
theorem bits_val_canon : ∀ l, canon l = true → bits (val l) = l
  | [], _ => by simp [val, bits]
  | [b], h => by
    have : b = true := h
    subst this
    rw [show val [true] = 1 from rfl, bits_pos (by decide)]
    simp [bits]
  | b :: c :: r, h => by
    have hv := val_pos_of_canon (c :: r) h (by simp)
    rw [val, bits_pos (by omega)]
    have e1 : ((b.toNat + 2 * val (c :: r)) % 2 == 1) = b := by cases b <;> simp <;> omega
    have e2 : (b.toNat + 2 * val (c :: r)) / 2 = val (c :: r) := by cases b <;> simp <;> omega
    rw [e1, e2, bits_val_canon (c :: r) h]

/-- Trimming is `bits` of the value. -/
theorem trim_bits (l : List Bool) : trim l = bits (val l) := by
  rw [← val_trim, bits_val_canon _ (canon_trim l)]

/-- The witness bits of `n` trim to `n`'s canonical bits. -/
theorem trim_bitsK {k n : Nat} (h : n < 2 ^ k) : trim (bitsK k n) = bits n := by
  rw [trim_bits, val_bitsK k n h]

-- ---------------------------------------------------------------------------
-- The converter: the circuit's bits to the runtime's bit list
-- ---------------------------------------------------------------------------

/-- `consTrimT b t = t (b [T] []) (λ h t'. cons b t)`: `consTrim` on the
    runtime's lists, by case on `t`. -/
def consTrimBody : OTerm :=
  .var 1 ⬝ₒ (.var 0 ⬝ₒ (bitsT [true]).toO ⬝ₒ (bitsT []).toO) ⬝ₒ
    absN [2, 3] (BitArith.consO (.var 0) (.var 1))

def consTrimT : Term := toTerm (absN [0, 1] consTrimBody)

theorem overrideC_two_0 (γ : Nat → Term) (a b : Term) : overrideC γ [0, 1] [a, b] 0 = a := rfl
theorem overrideC_two_1 (γ : Nat → Term) (a b : Term) : overrideC γ [0, 1] [a, b] 1 = b := rfl

/-- β: `consTrimT b t ↠ t (b [T] []) (K (K (cons b t)))`. -/
theorem consTrimT_beta (b t : Term) :
    WSteps (consTrimT ⬝ b ⬝ t) (t ⬝ (b ⬝ bitsT [true] ⬝ bitsT []) ⬝ (K ⬝ (K ⬝ consT b t))) := by
  have h := absN_beta_close [0, 1] consTrimBody (fun _ => K) [b, t] rfl
  simp only [consTrimBody, OTerm.close, close_toO, overrideC_two_0, overrideC_two_1] at h
  exact h

/-- **`consTrimT` is `consTrim`** on a bit and a bit list. -/
theorem consTrimT_red (b : Bool) : ∀ l : List Bool,
    WSteps (consTrimT ⬝ boolT b ⬝ bitsT l) (bitsT (consTrim b l))
  | [] => by
    refine (consTrimT_beta _ _).trans ?_
    refine (WSteps.single (.K _ _)).trans ?_
    refine (Compose.boolT_sel b _ _).trans ?_
    cases b <;> exact .refl _
  | c :: r => by
    refine (consTrimT_beta _ _).trans ?_
    show WSteps (K ⬝ pairT (boolT c) (bitsT r) ⬝ _ ⬝ _) _
    refine (WSteps.single (.left _ (.K _ _))).trans ?_
    refine (Compose.pairT_app _ _ _).trans ?_
    refine (WSteps.single (.left _ (.K _ _))).trans ?_
    exact WSteps.single (.K _ _)

/-- The step of the fold: `λ b t. consTrimT b (c t)`. -/
def toBitsBody (c : Term) : OTerm :=
  consTrimT.toO ⬝ₒ .var 0 ⬝ₒ (c.toO ⬝ₒ .var 1)

def toBitsG (c : Term) : Term := toTerm (absN [0, 1] (toBitsBody c))

theorem toBitsG_beta (c b t : Term) : WSteps (toBitsG c ⬝ b ⬝ t) (consTrimT ⬝ b ⬝ (c ⬝ t)) := by
  have h := absN_beta_close [0, 1] (toBitsBody c) (fun _ => K) [b, t] rfl
  simp only [toBitsBody, OTerm.close, close_toO, overrideC_two_0, overrideC_two_1] at h
  exact h

/-- **The converter**: the circuit's `k` bits (`boolsT`: a `pairT` chain,
    the last bit alone) to the runtime's canonical bit list. -/
def toBitsT : Nat → Term
  | 0 => K ⬝ nilT
  | 1 => pairT (bitsT [true]) (bitsT [])
  | k + 2 => S ⬝ I ⬝ (K ⬝ toBitsG (toBitsT (k + 1)))

theorem boolsT_cons₂ (b c : Bool) (r : List Bool) :
    boolsT (b :: c :: r) = pairT (boolT b) (boolsT (c :: r)) := rfl

/-- **`toBitsT k` on `k` bits is `trim`.** -/
theorem toBitsT_red : ∀ (k : Nat) (bs : List Bool), bs.length = k → 0 < k →
    WSteps (toBitsT k ⬝ boolsT bs) (bitsT (trim bs))
  | 0, _, _, h0 => absurd h0 (by decide)
  | 1, [b], _, _ => by
    show WSteps (pairT (bitsT [true]) (bitsT []) ⬝ boolT b) (bitsT (consTrim b []))
    refine (Compose.pairT_app _ _ _).trans ?_
    refine (Compose.boolT_sel b _ _).trans ?_
    cases b <;> exact .refl _
  | k + 2, b :: c :: r, hl, _ => by
    rw [boolsT_cons₂, toBitsT]
    refine (Compose.sI_app _ _).trans ?_
    refine (Compose.pairT_app _ _ _).trans ?_
    refine (toBitsG_beta _ _ _).trans ?_
    have ih := toBitsT_red (k + 1) (c :: r) (by simpa using hl) (Nat.succ_pos k)
    refine (WSteps.right _ ih).trans ?_
    exact consTrimT_red b _
  | 1, [], hl, _ => by cases hl
  | 1, _ :: _ :: _, hl, _ => by simp at hl
  | _ + 2, [], hl, _ => by cases hl
  | _ + 2, [_], hl, _ => by simp at hl

/-- `atomT` is a congruence for weak reduction. -/
theorem atomT_wsteps {b b' : Term} (h : WSteps b b') : WSteps (atomT b) (atomT b') :=
  WSteps.right _ (WSteps.right _ (WSteps.right _ (WSteps.right _ (WSteps.right _ h))))

-- ---------------------------------------------------------------------------
-- The verifier
-- ---------------------------------------------------------------------------

/-- `λ x ρ. eqn (nockToSki f (Atom (toBitsT k ρ))) x`, open. -/
def nockPredBody (f : Noun) (k : Nat) : OTerm :=
  eqnFix.toO ⬝ₒ ((nockToSki f).toO ⬝ₒ atomO ((toBitsT k).toO ⬝ₒ .var 1)) ⬝ₒ .var 0

/-- The verifier as a tree. -/
def nockPredV0 (f : Noun) (k : Nat) : Term := toTerm (absN [0, 1] (nockPredBody f k))

/-- **The verifier** of the statement "`*[n f] = p` for some `n` of `k`
    bits", `x = encNoun p`: the tree shared (`Nock2Ski/Share.lean`), so
    that the compiled formula's repeated subterms are loaded once. -/
def nockPredV (f : Noun) (k : Nat) : Term := share (nockPredV0 f k)

theorem nockPredV0_beta (f : Noun) (k : Nat) (x B : Term) :
    WSteps (nockPredV0 f k ⬝ x ⬝ B) (eqnFix ⬝ (nockToSki f ⬝ atomT (toBitsT k ⬝ B)) ⬝ x) := by
  have h := absN_beta_close [0, 1] (nockPredBody f k) (fun _ => K) [x, B] rfl
  simp only [nockPredBody, OTerm.close, close_toO, close_atomO, overrideC_two_0,
    overrideC_two_1] at h
  exact h

/-- β for the verifier: the sharing's βs, then the two formals. -/
theorem nockPredV_beta (f : Noun) (k : Nat) (x B : Term) :
    WSteps (nockPredV f k ⬝ x ⬝ B) (eqnFix ⬝ (nockToSki f ⬝ atomT (toBitsT k ⬝ B)) ⬝ x) :=
  (WSteps.left _ (WSteps.left _ (share_red _))).trans (nockPredV0_beta f k x B)

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

/-- **`nock_pred_complete`**: Nock's value `p` on the atom `n < 2^k` makes
    the verifier accept `encNoun p` on the `k` bits of `n`. -/
theorem nock_pred_complete {n k : Nat} {f p : Noun} (hk : 0 < k) (hn : n < 2 ^ k)
    (h : NockEval (.atom n) f (.val p)) :
    Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT (bitsK k n)) K := by
  rw [Compose.eval_K_iff]
  refine (nockPredV_beta f k _ _).trans ?_
  have hb : WSteps (toBitsT k ⬝ boolsT (bitsK k n)) (bitsT (bits n)) := by
    rw [← trim_bitsK hn]
    exact toBitsT_red k _ (bitsK_length k n) hk
  obtain ⟨ep, hp, he⟩ := embed_value_encNoun h
  have h1 : WSteps (nockToSki f ⬝ atomT (toBitsT k ⬝ boolsT (bitsK k n))) ep :=
    (WSteps.right _ (atomT_wsteps hb)).trans he
  have h2 := eqn_enc hp (enc_encNoun p)
  rw [decide_eq_true rfl] at h2
  exact (WSteps.left _ (WSteps.right _ h1)).trans h2

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

/-- `eqn` on `Err` answers `F`. -/
theorem eqn_err_run : BitArith.wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ errO ⬝ₒ .var 12) = .K ⬝ₒ .I := by
  decide +kernel

theorem eqn_err (b : Term) : WSteps (eqnFix ⬝ errT ⬝ b) (boolT false) := by
  have e := BitArith.run eqn_err_run (envR [eqnFix, K, b])
  simp only [OTerm.close, close_errO] at e
  rw [eqnGO_close _ rfl] at e
  exact (eqn_unfold _ _).trans e

/-- **The SKI-level verdict carried to Nock, values**: if `eqn` accepts the
    compiled formula's result on `encNoun (.atom n)` against `encNoun p`,
    then any Nock value of `f` on `n` is `p`. -/
theorem nock_pred_sound_val {f p q : Noun} {n : Nat}
    (h : WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝ encNoun p) K)
    (hq : NockEval (.atom n) f (.val q)) : q = p := by
  obtain ⟨eq, hqe, he⟩ := embed_value_encNoun hq
  have h2 : WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝ encNoun p) (boolT (decide (q = p))) :=
    (WSteps.left _ (WSteps.right _ he)).trans (eqn_enc hqe (enc_encNoun p))
  have hK := (Compose.wsteps_K_iff h2).mp h
  by_cases hqp : q = p
  · exact hqp
  · rw [decide_eq_false hqp] at hK
    exact absurd hK Compose.F_not_K

/-- **Crashes**: the same acceptance excludes a Nock crash on `n`. -/
theorem nock_pred_sound_crash {f p : Noun} {n : Nat}
    (h : WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝ encNoun p) K) :
    ¬ NockEval (.atom n) f .exit := fun hc => by
  have h2 : WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝ encNoun p) (boolT false) :=
    (WSteps.left _ (WSteps.right _ (embed_crash_encNoun hc))).trans (eqn_err _)
  exact Compose.F_not_K ((Compose.wsteps_K_iff h2).mp h)

/-- **`nock_pred_sound`**: the verifier accepting `encNoun p` on `k` bits
    shows an atom `n < 2^k`, the bits' value, on which the compiled formula
    is `eqn`-equal to `p`'s encoding; so Nock's value on `n`, if any, is
    `p`, and Nock does not crash on `n`. -/
theorem nock_pred_sound {f p : Noun} {k : Nat} {bs : List Bool} (hk : 0 < k) (hl : bs.length = k)
    (h : Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT bs) K) :
    ∃ n, n < 2 ^ k ∧ WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝ encNoun p) K ∧
      (∀ q, NockEval (.atom n) f (.val q) → q = p) ∧ ¬ NockEval (.atom n) f .exit := by
  rw [Compose.eval_K_iff] at h
  have hb : WSteps (toBitsT k ⬝ boolsT bs) (bitsT (bits (val bs))) := by
    rw [← trim_bits]
    exact toBitsT_red k bs hl hk
  have hred : WSteps (nockPredV f k ⬝ encNoun p ⬝ boolsT bs)
      (eqnFix ⬝ (nockToSki f ⬝ encNoun (.atom (val bs))) ⬝ encNoun p) :=
    (nockPredV_beta f k _ _).trans
      (WSteps.left _ (WSteps.right _ (WSteps.right _ (atomT_wsteps hb))))
  have hK := (Compose.wsteps_K_iff hred).mp h
  exact ⟨val bs, hl ▸ val_lt bs, hK, fun _ hq => nock_pred_sound_val hK hq,
    nock_pred_sound_crash hK⟩

end Nock2Ski
