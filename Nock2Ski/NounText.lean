import Nock2Ski.Compile

/-!
# Nouns in `[a b c]` notation

The parser and printer shared by `bench/NormCheck.lean` and
`bench/NockStatement.lean`: right-nested brackets, digits that may carry
dots.  Nothing here is proved; the exes are gates.
-/

namespace Nock2Ski.NounText

/-- Parse `[a b c]` notation, right-nested; digits may carry dots. -/
partial def parseNoun (s : String) : Except String Noun :=
  let toks := (s.replace "[" " [ " |>.replace "]" " ] ").splitOn " " |>.filter (· ≠ "")
  let rec item : List String → Except String (Noun × List String)
    | [] => .error "unexpected end"
    | "[" :: rest => do
      let rec items (ts : List String) (acc : List Noun) : Except String (List Noun × List String) :=
        match ts with
        | "]" :: r => .ok (acc.reverse, r)
        | [] => .error "unclosed ["
        | _ => do
          let (n, r) ← item ts
          items r (n :: acc)
      let (xs, r) ← items rest []
      match xs.reverse with
      | [] | [_] => .error "a cell needs two parts"
      | last :: before =>
        .ok (before.foldl (fun acc x => Noun.cell x acc) last, r)
    | "]" :: _ => .error "unexpected ]"
    | t :: rest =>
      match (t.replace "." "").toNat? with
      | some n => .ok (Noun.atom n, rest)
      | none => .error s!"not a number: {t}"
  match item toks with
  | .ok (n, []) => .ok n
  | .ok (_, _) => .error "trailing input"
  | .error e => .error e

partial def showNoun : Noun → String
  | .atom n => toString n
  | .cell h t =>
    let rec parts : Noun → List String
      | .cell h t => showNoun h :: parts t
      | n => [showNoun n]
    "[" ++ " ".intercalate (showNoun h :: parts t) ++ "]"

end Nock2Ski.NounText
