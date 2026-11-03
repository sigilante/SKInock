import Nock2Ski.Pred

open Nock
open Term
open Compose (boolT pairT)
open BitArith (val)

/-!
# A Nock program over a cell-shaped hidden subject (M4d)

M4c (`Nock2Ski/Pred.lean`) hides one atom: the circuit's `k` literal bits
are the subject.  Here the subject is a public **skeleton** with hidden
atoms at its leaves: `Skel` is a noun tree whose leaves are holes of `w`
bits each (`hole w`) or public constants (`lit n`).  The circuit still
holds one comb of `N` bits, `N` the skeleton's width (the holes' widths
summed), laid out hole by hole, left to right; the verifier cuts the comb
into the holes' slices (`takeT`, `dropT`: `sliceT N off w`), converts each
slice to an atom's canonical bits (`toBitsT w`, M4c's) and rebuilds the
subject with `cellT` and `atomT` around them (`skelT`):

    nockPredS f sk = share (λ x ρ. eqn (nockToSki f (skelT N sk 0 ρ)) x)

applied by the circuit to `x = encNoun p` and the bits.  `Skel.fill sk bs`
is the subject the bits name, and `skel_red` says the rebuilt term is
exactly `encNoun (sk.fill bs)`, so the compiled formula runs on the
encoding of a noun of the skeleton's shape whose hidden atoms are the
slices' values.  A single hole is M4c's statement unchanged
(`nockPredS_hole : nockPredS f (.hole k) = nockPredV f k`), and the
statement "I know atoms `a` and `b` of `k` bits each with `*[[a b] f] =
p`" is the skeleton `[?k ?k]` (`pairSkel k`, `nockPred2V`).

**Completeness** (`nock_predS_complete`, `nock_pred2_complete`): Nock's
value on the filled skeleton makes the verifier accept the bits.
**Soundness** (`nock_predS_sound`, `nock_pred2_sound`): acceptance on `N`
bits shows the atoms (below `2^w` each) on whose cell the compiled formula
is `eqn`-equal to `p`'s encoding, hence any Nock value on that subject is
`p` and Nock does not crash on it (`nock_pred_sound_val`,
`nock_pred_sound_crash`, over any subject).  Nock's termination on the
hidden subject is M4e's (`Nock2Ski/Converse.lean`, `nock_predS_sound_nock`,
`nock_pred2_sound_nock`), and the join to lean-ski's
`Circuit.predExport_sound` is `Nock2Ski/Circuit.lean`'s `predS_proof_nock`,
`pred2_proof_nock`.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Skeletons
-- ---------------------------------------------------------------------------

/-- A public subject skeleton: a hidden atom of `w` bits at each hole, a
    public noun at each literal. -/
inductive Skel where
  | hole (w : Nat)
  | lit (n : Noun)
  | cell (l r : Skel)
  deriving Repr, DecidableEq

namespace Skel

/-- The hidden bits: the holes' widths, left to right. -/
def width : Skel → Nat
  | hole w => w
  | lit _ => 0
  | cell l r => l.width + r.width

/-- Every hole has at least one bit (`toBitsT` converts no empty comb). -/
def ok : Skel → Bool
  | hole w => 0 < w
  | lit _ => true
  | cell l r => l.ok && r.ok

/-- The subject `bs` names: the holes filled left to right with the
    values of their slices. -/
def fill : Skel → List Bool → Noun
  | hole w, bs => .atom (val (bs.take w))
  | lit n, _ => n
  | cell l r, bs => .cell (l.fill bs) (r.fill (bs.drop l.width))

/-- The bits of a subject under the skeleton, when it fits: the witness. -/
def bitsOf : Skel → Noun → Except String (List Bool)
  | hole w, .atom n =>
    if n < 2 ^ w then .ok (bitsK w n) else .error s!"the atom {n} does not fit {w} bits"
  | hole _, .cell _ _ => .error "a cell where the skeleton hides an atom"
  | lit m, n => if m = n then .ok [] else .error "the subject differs from the skeleton's literal"
  | cell l r, .cell h t => do pure ((← l.bitsOf h) ++ (← r.bitsOf t))
  | cell _ _, .atom _ => .error "an atom where the skeleton has a cell"

end Skel

-- ---------------------------------------------------------------------------
-- Cutting the comb: `dropT`, `takeT`, `sliceT`
-- ---------------------------------------------------------------------------

theorem boolsT_cons_ne (b : Bool) {l : List Bool} (h : l ≠ []) :
    boolsT (b :: l) = pairT (boolT b) (boolsT l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- `dropT k ρ`: the comb after its first `k` bits.  `dropT 0 = I`;
    `dropT (k+1) = λρ. ρ (K (dropT k))`, the pair handing its tail on. -/
def dropT : Nat → Term
  | 0 => I
  | k + 1 => S ⬝ I ⬝ (K ⬝ (K ⬝ dropT k))

/-- **`dropT k` on a comb longer than `k` is `List.drop k`.** -/
theorem dropT_red : ∀ (k : Nat) (bs : List Bool), k < bs.length →
    WSteps (dropT k ⬝ boolsT bs) (boolsT (bs.drop k))
  | 0, _, _ => WSteps.single (.I _)
  | k + 1, b :: c :: r, h => by
    rw [boolsT_cons₂, dropT]
    refine (Compose.sI_app _ _).trans ?_
    refine (Compose.pairT_app _ _ _).trans ?_
    refine (WSteps.single (.left _ (.K _ _))).trans ?_
    exact dropT_red k (c :: r) (by simpa using h)
  | _ + 1, [], h => by simp at h
  | _ + 1, [_], h => by simp at h

/-- The step of `takeT`: `λ b r. pairT b (c r)`. -/
def takeBody (c : Term) : OTerm :=
  .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .var 0)) ⬝ₒ (.K ⬝ₒ (c.toO ⬝ₒ .var 1))

def takeG (c : Term) : Term := toTerm (absN [0, 1] (takeBody c))

theorem takeG_beta (c b r : Term) : WSteps (takeG c ⬝ b ⬝ r) (pairT b (c ⬝ r)) := by
  have h := absN_beta_close [0, 1] (takeBody c) (fun _ => K) [b, r] rfl
  simp only [takeBody, OTerm.close, close_toO, overrideC_two_0, overrideC_two_1] at h
  exact h

/-- `takeT k ρ`: the comb of the first `k` bits of a longer comb.
    `takeT 1 = λρ. ρ K` (the head alone), `takeT (k+2) = λρ. ρ (takeG
    (takeT (k+1)))`. -/
def takeT : Nat → Term
  | 0 => K ⬝ boolT false
  | 1 => S ⬝ I ⬝ (K ⬝ K)
  | k + 2 => S ⬝ I ⬝ (K ⬝ takeG (takeT (k + 1)))

/-- **`takeT k` on a comb longer than `k` is `List.take k`.** -/
theorem takeT_red : ∀ (k : Nat) (bs : List Bool), 0 < k → k < bs.length →
    WSteps (takeT k ⬝ boolsT bs) (boolsT (bs.take k))
  | 0, _, h0, _ => absurd h0 (by decide)
  | 1, b :: c :: r, _, _ => by
    rw [boolsT_cons₂, takeT]
    refine (Compose.sI_app _ _).trans ?_
    refine (Compose.pairT_app _ _ _).trans ?_
    exact WSteps.single (.K _ _)
  | k + 2, b :: c :: r, _, hl => by
    rw [boolsT_cons₂, takeT]
    refine (Compose.sI_app _ _).trans ?_
    refine (Compose.pairT_app _ _ _).trans ?_
    refine (takeG_beta _ _ _).trans ?_
    have ih := takeT_red (k + 1) (c :: r) (Nat.succ_pos k) (by simpa using hl)
    have hne : (c :: r).take (k + 1) ≠ [] := by simp
    rw [List.take_succ_cons, boolsT_cons_ne _ hne]
    exact WSteps.right _ (WSteps.right _ ih)
  | 1, [], _, hl => by simp at hl
  | 1, [_], _, hl => by simp at hl
  | _ + 2, [], _, hl => by simp at hl
  | _ + 2, [_], _, hl => by simp at hl

/-- The slice of the comb of `N` bits at offset `off`, `w` bits wide: the
    comb itself when it is the whole, `dropT` alone for the last hole,
    `takeT` after `dropT` otherwise. -/
def sliceT (N off w : Nat) (ρ : Term) : Term :=
  if off = 0 ∧ w = N then ρ
  else if off + w = N then dropT off ⬝ ρ
  else takeT w ⬝ (dropT off ⬝ ρ)

def sliceO (N off w : Nat) (ρ : OTerm) : OTerm :=
  if off = 0 ∧ w = N then ρ
  else if off + w = N then (dropT off).toO ⬝ₒ ρ
  else (takeT w).toO ⬝ₒ ((dropT off).toO ⬝ₒ ρ)

theorem close_sliceO (σ : Nat → Term) (N off w : Nat) (ρ : OTerm) :
    (sliceO N off w ρ).close σ = sliceT N off w (ρ.close σ) := by
  by_cases h1 : off = 0 ∧ w = N <;> by_cases h2 : off + w = N <;>
    simp [sliceO, sliceT, h1, h2, OTerm.close, close_toO]

/-- **The slice is `take w` of `drop off`.** -/
theorem sliceT_red {N off w : Nat} {bs : List Bool} (hw : 0 < w) (hN : off + w ≤ N)
    (hl : bs.length = N) :
    WSteps (sliceT N off w (boolsT bs)) (boolsT ((bs.drop off).take w)) := by
  unfold sliceT
  by_cases h1 : off = 0 ∧ w = N
  · rw [if_pos h1]
    obtain ⟨rfl, rfl⟩ := h1
    rw [List.drop_zero, List.take_of_length_le (by omega)]
    exact .refl _
  · rw [if_neg h1]
    by_cases h2 : off + w = N
    · rw [if_pos h2]
      rw [List.take_of_length_le (by rw [List.length_drop]; omega)]
      exact dropT_red off bs (by omega)
    · rw [if_neg h2]
      refine (WSteps.right _ (dropT_red off bs (by omega))).trans ?_
      exact takeT_red w _ hw (by rw [List.length_drop]; omega)

-- ---------------------------------------------------------------------------
-- The subject rebuilt around the slices
-- ---------------------------------------------------------------------------

/-- The subject as an open term over the comb `.var 1`: `Atom (toBitsT w
    (slice))` at a hole, the literal's encoding, `Cell` of the halves. -/
def skelO (N : Nat) : Skel → Nat → OTerm
  | .hole w, off => atomO ((toBitsT w).toO ⬝ₒ sliceO N off w (.var 1))
  | .lit n, _ => (encNoun n).toO
  | .cell l r, off => cellO (skelO N l off) (skelO N r (off + l.width))

/-- The same, closed, on the comb `ρ`. -/
def skelT (N : Nat) : Skel → Nat → Term → Term
  | .hole w, off, ρ => atomT (toBitsT w ⬝ sliceT N off w ρ)
  | .lit n, _, _ => encNoun n
  | .cell l r, off, ρ => cellT (skelT N l off ρ) (skelT N r (off + l.width) ρ)

theorem close_skelO (σ : Nat → Term) (N : Nat) : ∀ (sk : Skel) (off : Nat),
    (skelO N sk off).close σ = skelT N sk off (σ 1)
  | .hole w, off => by
    simp only [skelO, skelT, close_atomO, OTerm.close, close_toO, close_sliceO]
  | .lit n, _ => close_toO σ _
  | .cell l r, off => by
    rw [skelO, skelT, close_cellO, close_skelO σ N l, close_skelO σ N r]

/-- `pairT` and `cellT` are congruences for weak reduction. -/
theorem pairT_wsteps {h h' t t' : Term} (hh : WSteps h h') (ht : WSteps t t') :
    WSteps (pairT h t) (pairT h' t') :=
  (WSteps.left _ (WSteps.right _ (WSteps.right _ (WSteps.right _ hh)))).trans
    (WSteps.right _ (WSteps.right _ ht))

theorem cellT_wsteps {h h' t t' : Term} (hh : WSteps h h') (ht : WSteps t t') :
    WSteps (cellT h t) (cellT h' t') :=
  WSteps.right _ (WSteps.right _ (WSteps.right _ (pairT_wsteps hh ht)))

/-- **The rebuilt subject is the encoding of the filled skeleton.** -/
theorem skel_red {N : Nat} {bs : List Bool} (hl : bs.length = N) :
    ∀ (sk : Skel) (off : Nat), sk.ok = true → off + sk.width ≤ N →
      WSteps (skelT N sk off (boolsT bs)) (encNoun (sk.fill (bs.drop off)))
  | .hole w, off, hok, hN => by
    have hw : 0 < w := by simpa [Skel.ok] using hok
    have hN' : off + w ≤ N := by simpa [Skel.width] using hN
    have hs := sliceT_red hw hN' hl
    have hlen : ((bs.drop off).take w).length = w := by
      rw [List.length_take, List.length_drop]; omega
    have hb := toBitsT_red w _ hlen hw
    rw [trim_bits] at hb
    show WSteps (atomT (toBitsT w ⬝ sliceT N off w (boolsT bs)))
      (atomT (bitsT (bits (val ((bs.drop off).take w)))))
    exact atomT_wsteps ((WSteps.right _ hs).trans hb)
  | .lit _, _, _, _ => .refl _
  | .cell l r, off, hok, hN => by
    have hok' : l.ok = true ∧ r.ok = true := by simpa [Skel.ok] using hok
    have hN' : off + l.width + r.width ≤ N := by simp [Skel.width] at hN; omega
    show WSteps (cellT _ _)
      (cellT (encNoun (l.fill (bs.drop off))) (encNoun (r.fill ((bs.drop off).drop l.width))))
    rw [List.drop_drop]
    exact cellT_wsteps (skel_red hl l off hok'.1 (by omega)) (skel_red hl r _ hok'.2 hN')

-- ---------------------------------------------------------------------------
-- The verifier
-- ---------------------------------------------------------------------------

/-- `λ x ρ. eqn (nockToSki f (skelT N sk 0 ρ)) x`, open. -/
def nockPredSBody (f : Noun) (sk : Skel) : OTerm :=
  eqnFix.toO ⬝ₒ ((nockToSki f).toO ⬝ₒ skelO sk.width sk 0) ⬝ₒ .var 0

def nockPredS0 (f : Noun) (sk : Skel) : Term := toTerm (absN [0, 1] (nockPredSBody f sk))

/-- **The verifier** of "`*[s f] = p` for some `s` of the skeleton's shape
    with hidden atoms at its holes", `x = encNoun p`, shared. -/
def nockPredS (f : Noun) (sk : Skel) : Term := share (nockPredS0 f sk)

theorem nockPredS0_beta (f : Noun) (sk : Skel) (x B : Term) :
    WSteps (nockPredS0 f sk ⬝ x ⬝ B) (eqnFix ⬝ (nockToSki f ⬝ skelT sk.width sk 0 B) ⬝ x) := by
  have h := absN_beta_close [0, 1] (nockPredSBody f sk) (fun _ => K) [x, B] rfl
  simp only [nockPredSBody, OTerm.close, close_toO, close_skelO, overrideC_two_0,
    overrideC_two_1] at h
  exact h

theorem nockPredS_beta (f : Noun) (sk : Skel) (x B : Term) :
    WSteps (nockPredS f sk ⬝ x ⬝ B) (eqnFix ⬝ (nockToSki f ⬝ skelT sk.width sk 0 B) ⬝ x) :=
  (WSteps.left _ (WSteps.left _ (share_red _))).trans (nockPredS0_beta f sk x B)

/-- **A single hole is M4c's verifier**, term for term: the slice of the
    whole comb is the comb. -/
theorem nockPredS_hole (f : Noun) (k : Nat) : nockPredS f (.hole k) = nockPredV f k := by
  simp [nockPredS, nockPredV, nockPredS0, nockPredV0, nockPredSBody, nockPredBody, skelO,
    sliceO, Skel.width]

/-- The skeleton `[?k ?k]`: two hidden atoms of `k` bits each. -/
def pairSkel (k : Nat) : Skel := .cell (.hole k) (.hole k)

/-- **The verifier** of "I know atoms `a` and `b` of `k` bits each with
    `*[[a b] f] = p`". -/
def nockPred2V (f : Noun) (k : Nat) : Term := nockPredS f (pairSkel k)

-- ---------------------------------------------------------------------------
-- Completeness
-- ---------------------------------------------------------------------------

/-- **`nock_predS_complete`**: Nock's value `p` on the filled skeleton
    makes the verifier accept `encNoun p` on the bits. -/
theorem nock_predS_complete {f p : Noun} {sk : Skel} {bs : List Bool} (hok : sk.ok = true)
    (hl : bs.length = sk.width) (h : NockEval (sk.fill bs) f (.val p)) :
    Eval (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs) K := by
  rw [Compose.eval_K_iff]
  refine (nockPredS_beta f sk _ _).trans ?_
  have hs := skel_red hl sk 0 hok (by omega)
  rw [List.drop_zero] at hs
  obtain ⟨ep, hp, he⟩ := embed_value_encNoun h
  have h1 : WSteps (nockToSki f ⬝ skelT sk.width sk 0 (boolsT bs)) ep :=
    (WSteps.right _ hs).trans he
  have h2 := eqn_enc hp (enc_encNoun p)
  rw [decide_eq_true rfl] at h2
  exact (WSteps.left _ (WSteps.right _ h1)).trans h2

theorem pairSkel_fill {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (pairSkel k).fill (bitsK k a ++ bitsK k b) = .cell (.atom a) (.atom b) := by
  simp only [pairSkel, Skel.fill, Skel.width]
  rw [List.take_left' (bitsK_length k a), List.drop_left' (bitsK_length k a),
    List.take_of_length_le (Nat.le_of_eq (bitsK_length k b)), val_bitsK k a ha, val_bitsK k b hb]

/-- **`nock_pred2_complete`**: `*[[a b] f] = p` with `a, b < 2^k` makes the
    verifier accept `encNoun p` on the `k` bits of `a` then the `k` bits
    of `b`. -/
theorem nock_pred2_complete {a b k : Nat} {f p : Noun} (hk : 0 < k) (ha : a < 2 ^ k)
    (hb : b < 2 ^ k) (h : NockEval (.cell (.atom a) (.atom b)) f (.val p)) :
    Eval (nockPred2V f k ⬝ encNoun p ⬝ boolsT (bitsK k a ++ bitsK k b)) K := by
  apply nock_predS_complete (sk := pairSkel k)
  · simp [pairSkel, Skel.ok, hk]
  · simp [pairSkel, Skel.width, bitsK_length]
  · rw [pairSkel_fill ha hb]; exact h

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

/-- **`nock_predS_sound`**: the verifier accepting `encNoun p` on the bits
    shows the compiled formula `eqn`-equal to `p`'s encoding on the filled
    skeleton; so Nock's value on that subject, if any, is `p`, and Nock
    does not crash on it. -/
theorem nock_predS_sound {f p : Noun} {sk : Skel} {bs : List Bool} (hok : sk.ok = true)
    (hl : bs.length = sk.width) (h : Eval (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs) K) :
    WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (sk.fill bs)) ⬝ encNoun p) K ∧
      (∀ q, NockEval (sk.fill bs) f (.val q) → q = p) ∧ ¬ NockEval (sk.fill bs) f .exit := by
  rw [Compose.eval_K_iff] at h
  have hs := skel_red hl sk 0 hok (by omega)
  rw [List.drop_zero] at hs
  have hred : WSteps (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs)
      (eqnFix ⬝ (nockToSki f ⬝ encNoun (sk.fill bs)) ⬝ encNoun p) :=
    (nockPredS_beta f sk _ _).trans (WSteps.left _ (WSteps.right _ (WSteps.right _ hs)))
  have hK := (Compose.wsteps_K_iff hred).mp h
  exact ⟨hK, fun _ hq => nock_pred_sound_val hK hq, nock_pred_sound_crash hK⟩

/-- **`nock_pred2_sound`**: acceptance on `2k` bits shows atoms `a, b <
    2^k` on whose cell the compiled formula is `eqn`-equal to `p`'s
    encoding; any Nock value of `f` on `[a b]` is `p`, and Nock does not
    crash on `[a b]`. -/
theorem nock_pred2_sound {f p : Noun} {k : Nat} {bs : List Bool} (hk : 0 < k)
    (hl : bs.length = 2 * k) (h : Eval (nockPred2V f k ⬝ encNoun p ⬝ boolsT bs) K) :
    ∃ a b, a < 2 ^ k ∧ b < 2 ^ k ∧
      WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun (.cell (.atom a) (.atom b))) ⬝ encNoun p) K ∧
      (∀ q, NockEval (.cell (.atom a) (.atom b)) f (.val q) → q = p) ∧
      ¬ NockEval (.cell (.atom a) (.atom b)) f .exit := by
  have hok : (pairSkel k).ok = true := by simp [pairSkel, Skel.ok, hk]
  have hl' : bs.length = (pairSkel k).width := by simp [pairSkel, Skel.width]; omega
  obtain ⟨h1, h2, h3⟩ := nock_predS_sound hok hl' h
  have hfill : (pairSkel k).fill bs =
      .cell (.atom (val (bs.take k))) (.atom (val ((bs.drop k).take k))) := by
    simp [pairSkel, Skel.fill, Skel.width]
  rw [hfill] at h1 h2 h3
  refine ⟨_, _, ?_, ?_, h1, h2, h3⟩
  · have := val_lt (bs.take k)
    rwa [List.length_take, hl, Nat.min_eq_left (by omega)] at this
  · have := val_lt ((bs.drop k).take k)
    rwa [List.length_take, List.length_drop, hl, Nat.min_eq_left (by omega)] at this

end Nock2Ski
