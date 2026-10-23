include "MkfifoSpec.dfy"

// Executable MODE parser. It reads the string from left to right, as GNU
// mode_compile does, and builds the abstract syntax defined in MkfifoSpec.
// MkfifoModeProof shows that it inverts MkfifoSpec.Render.
module MkfifoModeCore {
  import S = MkfifoSpec

  datatype Option<T> = None | Some(value: T)

  predicate IsWhoChar(c: char) { c == 'u' || c == 'g' || c == 'o' || c == 'a' }
  predicate IsOpChar(c: char) { c == '+' || c == '-' || c == '=' }
  predicate IsCopyChar(c: char) { c == 'u' || c == 'g' || c == 'o' }
  predicate IsPermChar(c: char) { c == 'r' || c == 'w' || c == 'x' || c == 'X' || c == 's' || c == 't' }
  predicate IsOctalChar(c: char) { '0' <= c <= '7' }

  function WhoOf(c: char): S.Who
    requires IsWhoChar(c)
  {
    if c == 'u' then S.WhoU else if c == 'g' then S.WhoG else if c == 'o' then S.WhoO else S.WhoA
  }

  function OpOf(c: char): S.OpSym
    requires IsOpChar(c)
  {
    if c == '+' then S.OpAdd else if c == '-' then S.OpRemove else S.OpSet
  }

  function SrcOf(c: char): S.CopySrc
    requires IsCopyChar(c)
  {
    if c == 'u' then S.FromU else if c == 'g' then S.FromG else S.FromO
  }

  function PermOf(c: char): S.Perm
    requires IsPermChar(c)
  {
    if c == 'r' then S.PermR
    else if c == 'w' then S.PermW
    else if c == 'x' then S.PermX
    else if c == 'X' then S.PermCondX
    else if c == 's' then S.PermS
    else S.PermT
  }

  function DigitOf(c: char): S.OctDigit
    requires IsOctalChar(c)
  {
    c as int - '0' as int
  }

  // Each Take* function consumes the longest prefix of one character class.

  function TakeWho(s: string): (r: (seq<S.Who>, string))
    ensures |r.1| <= |s|
    decreases |s|
  {
    if |s| > 0 && IsWhoChar(s[0]) then
      var rest := TakeWho(s[1..]);
      ([WhoOf(s[0])] + rest.0, rest.1)
    else ([], s)
  }

  function TakePerms(s: string): (r: (seq<S.Perm>, string))
    ensures |r.1| <= |s|
    decreases |s|
  {
    if |s| > 0 && IsPermChar(s[0]) then
      var rest := TakePerms(s[1..]);
      ([PermOf(s[0])] + rest.0, rest.1)
    else ([], s)
  }

  function TakeDigits(s: string): (r: (seq<S.OctDigit>, string))
    ensures |r.1| <= |s|
    ensures |s| > 0 && IsOctalChar(s[0]) ==> |r.0| > 0
    decreases |s|
  {
    if |s| > 0 && IsOctalChar(s[0]) then
      var rest := TakeDigits(s[1..]);
      ([DigitOf(s[0])] + rest.0, rest.1)
    else ([], s)
  }

  // The text right after an operator: one copy letter, a digit run, or permission letters.
  function TakeRhs(s: string): (r: (S.Rhs, string))
    ensures |r.1| <= |s|
    ensures r.0.Octal? ==> |r.0.digits| > 0
  {
    if |s| > 0 && IsCopyChar(s[0]) then (S.Copy(SrcOf(s[0])), s[1..])
    else if |s| > 0 && IsOctalChar(s[0]) then
      var d := TakeDigits(s);
      (S.Octal(d.0), d.1)
    else
      var p := TakePerms(s);
      (S.Perms(p.0), p.1)
  }

  // One or more actions; s starts with an operator.
  function TakeActions(s: string): (r: (seq<S.Action>, string))
    requires |s| > 0 && IsOpChar(s[0])
    ensures |r.0| > 0 && |r.1| < |s|
    decreases |s|
  {
    var rhs := TakeRhs(s[1..]);
    var a := S.Action(OpOf(s[0]), rhs.0);
    if |rhs.1| > 0 && IsOpChar(rhs.1[0]) then
      var more := TakeActions(rhs.1);
      ([a] + more.0, more.1)
    else ([a], rhs.1)
  }

  // A clause and the unread rest, or None if the clause is malformed.
  function TakeClause(s: string): (r: Option<(S.Clause, string)>)
    ensures r.Some? ==> |r.value.1| < |s| && S.ClauseWellFormed(r.value.0)
  {
    var w := TakeWho(s);
    if |w.1| == 0 || !IsOpChar(w.1[0]) then None
    else
      var acts := TakeActions(w.1);
      var c := S.Clause(w.0, acts.0);
      if S.ClauseWellFormed(c) then Some((c, acts.1)) else None
  }

  // Clauses separated by ',' up to the end of s.
  function ParseClauses(s: string): (r: Option<seq<S.Clause>>)
    ensures r.Some? ==> |r.value| > 0 && forall c :: c in r.value ==> S.ClauseWellFormed(c)
    decreases |s|
  {
    match TakeClause(s)
    case None => None
    case Some(cr) =>
      var (c, rest) := cr;
      if |rest| == 0 then Some([c])
      else if rest[0] == ',' then
        match ParseClauses(rest[1..])
        case None => None
        case Some(cs) => Some([c] + cs)
      else None
  }

  function ParseMode(s: string): (r: Option<S.ModeExpr>)
    ensures r.Some? ==> S.WellFormed(r.value)
  {
    if |s| > 0 && IsOctalChar(s[0]) then
      var d := TakeDigits(s);
      if |d.1| == 0 && S.OctalValue(d.0) <= S.ALLM then Some(S.Absolute(d.0)) else None
    else
      match ParseClauses(s)
      case None => None
      case Some(cs) => Some(S.Symbolic(cs))
  }
}
