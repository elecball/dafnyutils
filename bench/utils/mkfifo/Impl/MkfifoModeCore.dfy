include "../Spec/MkfifoSpec.dfy"

// Executable MODE parser. It reads the string from left to right, as GNU
// mode_compile does, and builds the abstract syntax defined in MkfifoSpec.
// MkfifoModeProof shows that it inverts MkfifoSpec.Render.
//
// The recursive functions define the parser for the proofs. At run time
// ParseMode and ComputeMeaning use the loops at the end of this module: they
// walk indices of the string, so a long MODE neither grows the call stack nor
// copies the string once per letter.
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
  } by method {
    assert s[0..] == s;
    if |s| > 0 && IsOctalChar(s[0]) {
      var ds, j := TakeDigitsAt(s, 0);
      if j == |s| {
        var _, within := OctalUpTo(ds);
        r := if within then Some(S.Absolute(ds)) else None;
      } else {
        r := None;
      }
    } else {
      var cs := ParseClausesFrom(s);
      r := if cs.None? then None else Some(S.Symbolic(cs.value));
    }
  }

  // ---------------------------------------------------------------------------
  // Loops used at run time. Each one ends where the function of the same name
  // would stop: Take*At(s, i) returns the value of Take*(s[i..]) and the index
  // of the unread rest.
  // ---------------------------------------------------------------------------

  method TakeWhoAt(s: string, i: nat) returns (xs: seq<S.Who>, j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
    ensures TakeWho(s[i..]).0 == xs && TakeWho(s[i..]).1 == s[j..]
  {
    xs, j := [], i;
    assert [] + TakeWho(s[i..]).0 == TakeWho(s[i..]).0;
    while j < |s| && IsWhoChar(s[j])
      invariant i <= j <= |s|
      invariant TakeWho(s[i..]).0 == xs + TakeWho(s[j..]).0
      invariant TakeWho(s[i..]).1 == TakeWho(s[j..]).1
    {
      ghost var rest := TakeWho(s[j + 1..]);
      assert s[j..][1..] == s[j + 1..];
      assert TakeWho(s[j..]).0 == [WhoOf(s[j])] + rest.0 && TakeWho(s[j..]).1 == rest.1;
      assert xs + ([WhoOf(s[j])] + rest.0) == (xs + [WhoOf(s[j])]) + rest.0;
      xs, j := xs + [WhoOf(s[j])], j + 1;
    }
    assert xs + [] == xs;
  }

  method TakePermsAt(s: string, i: nat) returns (xs: seq<S.Perm>, j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
    ensures TakePerms(s[i..]).0 == xs && TakePerms(s[i..]).1 == s[j..]
  {
    xs, j := [], i;
    assert [] + TakePerms(s[i..]).0 == TakePerms(s[i..]).0;
    while j < |s| && IsPermChar(s[j])
      invariant i <= j <= |s|
      invariant TakePerms(s[i..]).0 == xs + TakePerms(s[j..]).0
      invariant TakePerms(s[i..]).1 == TakePerms(s[j..]).1
    {
      ghost var rest := TakePerms(s[j + 1..]);
      assert s[j..][1..] == s[j + 1..];
      assert TakePerms(s[j..]).0 == [PermOf(s[j])] + rest.0 && TakePerms(s[j..]).1 == rest.1;
      assert xs + ([PermOf(s[j])] + rest.0) == (xs + [PermOf(s[j])]) + rest.0;
      xs, j := xs + [PermOf(s[j])], j + 1;
    }
    assert xs + [] == xs;
  }

  method TakeDigitsAt(s: string, i: nat) returns (xs: seq<S.OctDigit>, j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
    ensures TakeDigits(s[i..]).0 == xs && TakeDigits(s[i..]).1 == s[j..]
  {
    xs, j := [], i;
    assert [] + TakeDigits(s[i..]).0 == TakeDigits(s[i..]).0;
    while j < |s| && IsOctalChar(s[j])
      invariant i <= j <= |s|
      invariant TakeDigits(s[i..]).0 == xs + TakeDigits(s[j..]).0
      invariant TakeDigits(s[i..]).1 == TakeDigits(s[j..]).1
    {
      ghost var rest := TakeDigits(s[j + 1..]);
      assert s[j..][1..] == s[j + 1..];
      assert TakeDigits(s[j..]).0 == [DigitOf(s[j])] + rest.0 && TakeDigits(s[j..]).1 == rest.1;
      assert xs + ([DigitOf(s[j])] + rest.0) == (xs + [DigitOf(s[j])]) + rest.0;
      xs, j := xs + [DigitOf(s[j])], j + 1;
    }
    assert xs + [] == xs;
  }

  method TakeRhsAt(s: string, i: nat) returns (rhs: S.Rhs, j: nat)
    requires i <= |s|
    ensures i <= j <= |s|
    ensures TakeRhs(s[i..]).0 == rhs && TakeRhs(s[i..]).1 == s[j..]
  {
    if i < |s| && IsCopyChar(s[i]) {
      assert s[i..][1..] == s[i + 1..];
      rhs, j := S.Copy(SrcOf(s[i])), i + 1;
    } else if i < |s| && IsOctalChar(s[i]) {
      var ds;
      ds, j := TakeDigitsAt(s, i);
      rhs := S.Octal(ds);
    } else {
      var ps;
      ps, j := TakePermsAt(s, i);
      rhs := S.Perms(ps);
    }
  }

  method TakeActionsAt(s: string, i: nat) returns (acts: seq<S.Action>, j: nat)
    requires i < |s| && IsOpChar(s[i])
    ensures i < j <= |s|
    ensures TakeActions(s[i..]).0 == acts && TakeActions(s[i..]).1 == s[j..]
  {
    acts := [];
    var k := i;
    assert [] + TakeActions(s[i..]).0 == TakeActions(s[i..]).0;
    while true
      invariant i <= k < |s| && IsOpChar(s[k])
      invariant TakeActions(s[i..]).0 == acts + TakeActions(s[k..]).0
      invariant TakeActions(s[i..]).1 == TakeActions(s[k..]).1
      decreases |s| - k
    {
      assert s[k..][1..] == s[k + 1..];
      var rhs, m := TakeRhsAt(s, k + 1);
      var a := S.Action(OpOf(s[k]), rhs);
      if m < |s| && IsOpChar(s[m]) {
        ghost var more := TakeActions(s[m..]);
        assert TakeActions(s[k..]).0 == [a] + more.0 && TakeActions(s[k..]).1 == more.1;
        assert acts + ([a] + more.0) == (acts + [a]) + more.0;
        acts, k := acts + [a], m;
      } else {
        assert TakeActions(s[k..]).0 == [a] && TakeActions(s[k..]).1 == s[m..];
        acts, j := acts + [a], m;
        return;
      }
    }
  }

  method TakeClauseAt(s: string, i: nat) returns (r: Option<(S.Clause, nat)>)
    requires i <= |s|
    ensures r.None? <==> TakeClause(s[i..]).None?
    ensures r.Some? ==> i < r.value.1 <= |s|
    ensures r.Some? ==> TakeClause(s[i..]).value.0 == r.value.0 && TakeClause(s[i..]).value.1 == s[r.value.1..]
  {
    var who, k := TakeWhoAt(s, i);
    if k == |s| || !IsOpChar(s[k]) {
      return None;
    }
    var acts, m := TakeActionsAt(s, k);
    var c := S.Clause(who, acts);
    var ok := CheckClause(c);
    r := if ok then Some((c, m)) else None;
  }

  ghost function Prepend(acc: seq<S.Clause>, r: Option<seq<S.Clause>>): Option<seq<S.Clause>>
  {
    match r
    case None => None
    case Some(cs) => Some(acc + cs)
  }

  method ParseClausesFrom(s: string) returns (r: Option<seq<S.Clause>>)
    ensures r == ParseClauses(s)
  {
    var acc: seq<S.Clause> := [];
    var k := 0;
    assert s[0..] == s;
    match ParseClauses(s) {
      case None =>
      case Some(cs) => assert [] + cs == cs;
    }
    while true
      invariant 0 <= k <= |s|
      invariant ParseClauses(s) == Prepend(acc, ParseClauses(s[k..]))
      decreases |s| - k
    {
      var taken := TakeClauseAt(s, k);
      if taken.None? {
        return None;
      }
      var c, m := taken.value.0, taken.value.1;
      if m == |s| {
        return Some(acc + [c]);
      } else if s[m] == ',' {
        assert s[m..][1..] == s[m + 1..];
        match ParseClauses(s[m + 1..]) {
          case None =>
          case Some(cs) => assert acc + ([c] + cs) == (acc + [c]) + cs;
        }
        acc, k := acc + [c], m + 1;
      } else {
        return None;
      }
    }
  }

  method CheckClause(c: S.Clause) returns (ok: bool)
    ensures ok == S.ClauseWellFormed(c)
  {
    var n := |c.actions|;
    ok := n > 0;
    var t := 0;
    while t < n
      invariant 0 <= t <= n
      invariant ok == (n > 0 && forall q :: 0 <= q < t ==> S.ActionWellFormed(c.who, c.actions[q], q == n - 1))
    {
      var a := CheckAction(c.who, c.actions[t], t == n - 1);
      ok := ok && a;
      t := t + 1;
    }
  }

  method CheckAction(who: seq<S.Who>, a: S.Action, isLast: bool) returns (ok: bool)
    ensures ok == S.ActionWellFormed(who, a, isLast)
  {
    match a.rhs
    case Octal(ds) =>
      var _, within := OctalUpTo(ds);
      ok := |ds| > 0 && within && |who| == 0 && isLast;
    case _ =>
      ok := true;
  }

  // The value of ds, read from the left. Like mode_compile, it stops as soon as
  // the value passes 07777, so a long run of digits never builds a big number.
  method OctalUpTo(ds: seq<S.OctDigit>) returns (v: nat, within: bool)
    ensures within == (S.OctalValue(ds) <= S.ALLM)
    ensures within ==> v == S.OctalValue(ds) && v <= 4095
  {
    v := 0;
    var t := 0;
    while t < |ds|
      invariant 0 <= t <= |ds|
      invariant v == S.OctalValue(ds[..t]) && v <= S.ALLM
    {
      assert ds[..t + 1][..t] == ds[..t];
      v := v * 8 + ds[t];
      if v > S.ALLM {
        OctalPrefixAtMost(ds, t + 1);
        return v, false;
      }
      t := t + 1;
    }
    assert ds[..t] == ds;
    within := true;
  }

  lemma OctalPrefixAtMost(ds: seq<S.OctDigit>, t: nat)
    requires t <= |ds|
    ensures S.OctalValue(ds[..t]) <= S.OctalValue(ds)
    decreases |ds| - t
  {
    if t < |ds| {
      assert ds[..t + 1][..t] == ds[..t];
      OctalPrefixAtMost(ds, t + 1);
    } else {
      assert ds[..t] == ds;
    }
  }

  // ---------------------------------------------------------------------------
  // MkfifoSpec.Meaning, computed with loops. The who and permission lists are
  // folded from the right, as WhoBits and PermsBits are defined.
  // ---------------------------------------------------------------------------

  method ComputeMeaning(e: S.ModeExpr, umask: bv32) returns (bits: bv32)
    requires S.WellFormed(e)
    ensures bits == S.Meaning(e, umask)
  {
    match e
    case Absolute(ds) =>
      var v, _ := OctalUpTo(ds);
      bits := v as bv32;
    case Symbolic(cs) =>
      bits := S.MKFIFO_BASE_MODE;
      var t := 0;
      while t < |cs|
        invariant 0 <= t <= |cs|
        invariant S.ApplyClauses(S.MKFIFO_BASE_MODE, umask, cs) == S.ApplyClauses(bits, umask, cs[t..])
      {
        assert cs[t..][1..] == cs[t + 1..];
        S.ClauseActionsBounded(cs[t]);
        bits := ApplyClause(bits, umask, cs[t]);
        t := t + 1;
      }
      assert cs[t..] == [];
  }

  method ApplyClause(cur: bv32, umask: bv32, c: S.Clause) returns (r: bv32)
    requires S.ActionsBounded(c.actions)
    ensures r == S.ApplyActions(cur, umask, c.who, c.actions)
  {
    var who := WhoBitsOf(c.who);
    r := cur;
    var t := 0;
    while t < |c.actions|
      invariant 0 <= t <= |c.actions|
      invariant S.ActionsBounded(c.actions[t..])
      invariant S.ApplyActions(cur, umask, c.who, c.actions) == S.ApplyActions(r, umask, c.who, c.actions[t..])
    {
      assert c.actions[t..][1..] == c.actions[t + 1..];
      r := ApplyOne(r, umask, c.who, who, c.actions[t]);
      t := t + 1;
    }
    assert c.actions[t..] == [];
  }

  // The methods from ApplyOne to RhsOctal hide the other definitions of the
  // spec module and prove one small step each: proved together, the steps do
  // not finish within the solver's time limit (30 s per declaration).
  method ApplyOne(cur: bv32, umask: bv32, who: seq<S.Who>, whoBits: bv32, a: S.Action) returns (r: bv32)
    requires whoBits == S.WhoBits(who)
    requires a.rhs.Octal? ==> S.OctalValue(a.rhs.digits) <= S.ALLM
    ensures r == S.ApplyAction(cur, umask, who, a)
  {
    var scope := ScopeOf(who, whoBits, a);
    var rhs := RhsBitsOf(a.rhs, cur);
    r := ApplyWith(cur, umask, who, a, scope, rhs);
  }

  method ScopeOf(who: seq<S.Who>, whoBits: bv32, a: S.Action) returns (scope: bv32)
    requires whoBits == S.WhoBits(who)
    ensures scope == S.ActionScope(who, a)
  {
    hide *;
    reveal S.ActionScope;
    scope := if a.rhs.Octal? then S.MODE_BITS else whoBits;
  }

  // ApplyAction once the scope and the proposed bits are known, one operator
  // at a time.
  method ApplyWith(cur: bv32, umask: bv32, who: seq<S.Who>, a: S.Action, scope: bv32, rhs: bv32)
    returns (r: bv32)
    requires scope == S.ActionScope(who, a)
    requires a.rhs.Octal? ==> S.OctalValue(a.rhs.digits) <= S.ALLM
    requires rhs == S.RhsBits(a.rhs, cur)
    ensures r == S.ApplyAction(cur, umask, who, a)
  {
    hide *;
    match a.op
    case OpSet => r := ApplySet(cur, umask, who, a, scope, rhs);
    case OpAdd => r := ApplyAdd(cur, umask, who, a, scope, rhs);
    case OpRemove => r := ApplyRemove(cur, umask, who, a, scope, rhs);
  }

  method ApplySet(cur: bv32, umask: bv32, who: seq<S.Who>, a: S.Action, scope: bv32, rhs: bv32)
    returns (r: bv32)
    requires a.op.OpSet? && scope == S.ActionScope(who, a)
    requires a.rhs.Octal? ==> S.OctalValue(a.rhs.digits) <= S.ALLM
    requires rhs == S.RhsBits(a.rhs, cur)
    ensures r == S.ApplyAction(cur, umask, who, a)
  {
    hide *;
    reveal S.ApplyAction;
    if scope != 0 {
      r := (cur & !scope) | (rhs & scope);
    } else {
      r := rhs & !umask;
    }
  }

  method ApplyAdd(cur: bv32, umask: bv32, who: seq<S.Who>, a: S.Action, scope: bv32, rhs: bv32)
    returns (r: bv32)
    requires a.op.OpAdd? && scope == S.ActionScope(who, a)
    requires a.rhs.Octal? ==> S.OctalValue(a.rhs.digits) <= S.ALLM
    requires rhs == S.RhsBits(a.rhs, cur)
    ensures r == S.ApplyAction(cur, umask, who, a)
  {
    hide *;
    reveal S.ApplyAction;
    r := cur | (rhs & (if scope != 0 then scope else !umask));
  }

  method ApplyRemove(cur: bv32, umask: bv32, who: seq<S.Who>, a: S.Action, scope: bv32, rhs: bv32)
    returns (r: bv32)
    requires a.op.OpRemove? && scope == S.ActionScope(who, a)
    requires a.rhs.Octal? ==> S.OctalValue(a.rhs.digits) <= S.ALLM
    requires rhs == S.RhsBits(a.rhs, cur)
    ensures r == S.ApplyAction(cur, umask, who, a)
  {
    hide *;
    reveal S.ApplyAction;
    r := cur & !(rhs & (if scope != 0 then scope else !umask));
  }

  method RhsBitsOf(rhs: S.Rhs, cur: bv32) returns (r: bv32)
    requires rhs.Octal? ==> S.OctalValue(rhs.digits) <= S.ALLM
    ensures r == S.RhsBits(rhs, cur)
  {
    hide *;
    match rhs
    case Perms(ps) => r := RhsPerms(ps, cur);
    case Copy(src) => r := RhsCopy(src, cur);
    case Octal(ds) => r := RhsOctal(ds, cur);
  }

  method RhsPerms(ps: seq<S.Perm>, cur: bv32) returns (r: bv32)
    ensures r == S.RhsBits(S.Perms(ps), cur)
  {
    hide *;
    reveal S.RhsBits;
    var bits := PermsBitsOf(ps);
    var condX := CondXOf(ps, cur);
    r := bits | (if condX then S.EXEC_BITS else 0);
  }

  // Whether 'X' adds execute bits (see MkfifoSpec.RhsBits).
  method CondXOf(ps: seq<S.Perm>, cur: bv32) returns (b: bool)
    ensures b == (S.PermCondX in ps && cur & S.EXEC_BITS != 0)
  {
    b := S.PermCondX in ps && cur & S.EXEC_BITS != 0;
  }

  method RhsCopy(src: S.CopySrc, cur: bv32) returns (r: bv32)
    ensures r == S.RhsBits(S.Copy(src), cur)
  {
    r := S.CopyBits(src, cur);
  }

  method RhsOctal(ds: seq<S.OctDigit>, cur: bv32) returns (r: bv32)
    requires S.OctalValue(ds) <= S.ALLM
    ensures r == S.RhsBits(S.Octal(ds), cur)
  {
    var v, _ := OctalUpTo(ds);
    r := v as bv32;
  }

  method WhoBitsOf(ws: seq<S.Who>) returns (r: bv32)
    ensures r == S.WhoBits(ws)
  {
    r := 0;
    var t := |ws|;
    while t > 0
      invariant 0 <= t <= |ws|
      invariant r == S.WhoBits(ws[t..])
    {
      t := t - 1;
      assert ws[t..][1..] == ws[t + 1..];
      r := S.WhoMask(ws[t]) | r;
    }
    assert ws[0..] == ws;
  }

  method PermsBitsOf(ps: seq<S.Perm>) returns (r: bv32)
    ensures r == S.PermsBits(ps)
  {
    r := 0;
    var t := |ps|;
    while t > 0
      invariant 0 <= t <= |ps|
      invariant r == S.PermsBits(ps[t..])
    {
      t := t - 1;
      assert ps[t..][1..] == ps[t + 1..];
      r := S.PermBits(ps[t]) | r;
    }
    assert ps[0..] == ps;
  }
}
