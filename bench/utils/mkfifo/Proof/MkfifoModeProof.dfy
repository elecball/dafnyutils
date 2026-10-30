include "../Spec/MkfifoSpec.dfy"
include "../Impl/MkfifoModeCore.dfy"

// The parser in MkfifoModeCore inverts MkfifoSpec.Render:
// - completeness: ParseMode(Render(e)) == Some(e) for every well-formed e;
// - soundness: ParseMode(s) == Some(e) implies Render(e) == s.
// Together they make "invalid mode" exact and give each valid MODE one meaning.
module MkfifoModeProof {
  import S = MkfifoSpec
  import P = MkfifoModeCore

  // ---------------------------------------------------------------------------
  // Characters
  // ---------------------------------------------------------------------------

  lemma WhoCharRoundTrip(w: S.Who)
    ensures P.IsWhoChar(S.WhoChar(w)) && P.WhoOf(S.WhoChar(w)) == w
    ensures !P.IsOpChar(S.WhoChar(w)) && !P.IsOctalChar(S.WhoChar(w))
  {}

  lemma OpCharRoundTrip(o: S.OpSym)
    ensures P.IsOpChar(S.OpChar(o)) && P.OpOf(S.OpChar(o)) == o
    ensures !P.IsWhoChar(S.OpChar(o)) && !P.IsPermChar(S.OpChar(o))
    ensures !P.IsCopyChar(S.OpChar(o)) && !P.IsOctalChar(S.OpChar(o))
  {}

  lemma PermCharRoundTrip(p: S.Perm)
    ensures P.IsPermChar(S.PermChar(p)) && P.PermOf(S.PermChar(p)) == p
    ensures !P.IsCopyChar(S.PermChar(p)) && !P.IsOctalChar(S.PermChar(p))
  {}

  lemma SrcCharRoundTrip(src: S.CopySrc)
    ensures P.IsCopyChar(S.SrcChar(src)) && P.SrcOf(S.SrcChar(src)) == src
  {}

  lemma DigitCharRoundTrip(d: S.OctDigit)
    ensures P.IsOctalChar(S.DigitChar(d)) && P.DigitOf(S.DigitChar(d)) == d
    ensures !P.IsCopyChar(S.DigitChar(d))
  {}

  lemma WhoOfRoundTrip(c: char)
    requires P.IsWhoChar(c)
    ensures S.WhoChar(P.WhoOf(c)) == c
  {}

  lemma OpOfRoundTrip(c: char)
    requires P.IsOpChar(c)
    ensures S.OpChar(P.OpOf(c)) == c
  {}

  lemma PermOfRoundTrip(c: char)
    requires P.IsPermChar(c)
    ensures S.PermChar(P.PermOf(c)) == c
  {}

  lemma SrcOfRoundTrip(c: char)
    requires P.IsCopyChar(c)
    ensures S.SrcChar(P.SrcOf(c)) == c
  {}

  lemma DigitOfRoundTrip(c: char)
    requires P.IsOctalChar(c)
    ensures S.DigitChar(P.DigitOf(c)) == c
  {}

  // ---------------------------------------------------------------------------
  // Completeness: reading a rendered prefix gives back the syntax
  // ---------------------------------------------------------------------------

  lemma TakeWhoOfRender(ws: seq<S.Who>, rest: string)
    requires |rest| == 0 || !P.IsWhoChar(rest[0])
    ensures P.TakeWho(S.RenderWho(ws) + rest) == (ws, rest)
    decreases |ws|
  {
    if |ws| > 0 {
      WhoCharRoundTrip(ws[0]);
      var s := S.RenderWho(ws) + rest;
      assert s == [S.WhoChar(ws[0])] + (S.RenderWho(ws[1..]) + rest);
      assert s[1..] == S.RenderWho(ws[1..]) + rest;
      TakeWhoOfRender(ws[1..], rest);
      assert [ws[0]] + ws[1..] == ws;
    } else {
      assert S.RenderWho(ws) + rest == rest;
    }
  }

  lemma TakePermsOfRender(ps: seq<S.Perm>, rest: string)
    requires |rest| == 0 || !P.IsPermChar(rest[0])
    ensures P.TakePerms(S.RenderPerms(ps) + rest) == (ps, rest)
    decreases |ps|
  {
    if |ps| > 0 {
      PermCharRoundTrip(ps[0]);
      var s := S.RenderPerms(ps) + rest;
      assert s == [S.PermChar(ps[0])] + (S.RenderPerms(ps[1..]) + rest);
      assert s[1..] == S.RenderPerms(ps[1..]) + rest;
      TakePermsOfRender(ps[1..], rest);
      assert [ps[0]] + ps[1..] == ps;
    } else {
      assert S.RenderPerms(ps) + rest == rest;
    }
  }

  lemma TakeDigitsOfRender(ds: seq<S.OctDigit>, rest: string)
    requires |rest| == 0 || !P.IsOctalChar(rest[0])
    ensures P.TakeDigits(S.RenderDigits(ds) + rest) == (ds, rest)
    decreases |ds|
  {
    if |ds| > 0 {
      DigitCharRoundTrip(ds[0]);
      var s := S.RenderDigits(ds) + rest;
      assert s == [S.DigitChar(ds[0])] + (S.RenderDigits(ds[1..]) + rest);
      assert s[1..] == S.RenderDigits(ds[1..]) + rest;
      TakeDigitsOfRender(ds[1..], rest);
      assert [ds[0]] + ds[1..] == ds;
    } else {
      assert S.RenderDigits(ds) + rest == rest;
    }
  }

  // After a right-hand side comes an operator, ',' or the end.
  predicate RhsFollower(rest: string)
  {
    |rest| == 0 || rest[0] == ',' || P.IsOpChar(rest[0])
  }

  lemma TakeRhsOfRender(rhs: S.Rhs, rest: string)
    requires RhsFollower(rest)
    requires rhs.Octal? ==> |rhs.digits| > 0
    ensures P.TakeRhs(S.RenderRhs(rhs) + rest) == (rhs, rest)
  {
    var s := S.RenderRhs(rhs) + rest;
    match rhs
    case Copy(src) =>
      SrcCharRoundTrip(src);
      assert s[0] == S.SrcChar(src) && s[1..] == rest;
    case Octal(ds) =>
      DigitCharRoundTrip(ds[0]);
      assert s[0] == S.DigitChar(ds[0]);
      TakeDigitsOfRender(ds, rest);
    case Perms(ps) =>
      if |ps| > 0 {
        PermCharRoundTrip(ps[0]);
        assert s[0] == S.PermChar(ps[0]);
      } else {
        assert s == rest;
        assert |s| == 0 || s[0] == ',' || P.IsOpChar(s[0]);
      }
      assert |s| == 0 || (!P.IsCopyChar(s[0]) && !P.IsOctalChar(s[0]));
      assert P.TakeRhs(s) == (S.Perms(P.TakePerms(s).0), P.TakePerms(s).1);
      TakePermsOfRender(ps, rest);
  }

  predicate DigitsNonempty(as_: seq<S.Action>)
  {
    forall i :: 0 <= i < |as_| ==> as_[i].rhs.Octal? ==> |as_[i].rhs.digits| > 0
  }

  lemma TakeActionsOfRender(as_: seq<S.Action>, rest: string)
    requires |as_| > 0 && DigitsNonempty(as_)
    requires |rest| == 0 || rest[0] == ','
    ensures |S.RenderActions(as_) + rest| > 0 && P.IsOpChar((S.RenderActions(as_) + rest)[0])
    ensures P.TakeActions(S.RenderActions(as_) + rest) == (as_, rest)
    decreases |as_|
  {
    var a := as_[0];
    var tail := as_[1..];
    OpCharRoundTrip(a.op);
    var after := S.RenderActions(tail) + rest;
    var s := S.RenderActions(as_) + rest;
    assert s == [S.OpChar(a.op)] + (S.RenderRhs(a.rhs) + after);
    assert s[0] == S.OpChar(a.op);
    assert s[1..] == S.RenderRhs(a.rhs) + after;
    if |tail| > 0 {
      assert DigitsNonempty(tail) by {
        forall i | 0 <= i < |tail| ensures tail[i].rhs.Octal? ==> |tail[i].rhs.digits| > 0 {
          assert tail[i] == as_[i + 1];
        }
      }
      TakeActionsOfRender(tail, rest);
      TakeRhsOfRender(a.rhs, after);
      assert [a] + tail == as_;
    } else {
      assert after == rest;
      TakeRhsOfRender(a.rhs, rest);
      assert as_ == [a];
    }
  }

  lemma ClauseDigitsNonempty(c: S.Clause)
    requires S.ClauseWellFormed(c)
    ensures DigitsNonempty(c.actions)
  {
    forall i | 0 <= i < |c.actions| && c.actions[i].rhs.Octal?
      ensures |c.actions[i].rhs.digits| > 0
    {
      assert S.ActionWellFormed(c.who, c.actions[i], i == |c.actions| - 1);
    }
  }

  lemma TakeClauseOfRender(c: S.Clause, rest: string)
    requires S.ClauseWellFormed(c)
    requires |rest| == 0 || rest[0] == ','
    ensures P.TakeClause(S.RenderClause(c) + rest) == P.Some((c, rest))
  {
    ClauseDigitsNonempty(c);
    var acts := S.RenderActions(c.actions) + rest;
    TakeActionsOfRender(c.actions, rest);
    OpCharRoundTrip(c.actions[0].op);
    assert S.RenderClause(c) + rest == S.RenderWho(c.who) + acts;
    TakeWhoOfRender(c.who, acts);
  }

  lemma ParseClausesOfRender(cs: seq<S.Clause>)
    requires |cs| > 0 && forall c :: c in cs ==> S.ClauseWellFormed(c)
    ensures P.ParseClauses(S.RenderClauses(cs)) == P.Some(cs)
    decreases |cs|
  {
    assert cs[0] in cs;
    if |cs| == 1 {
      TakeClauseOfRender(cs[0], "");
      assert cs == [cs[0]];
      assert S.RenderClauses(cs) == S.RenderClause(cs[0]) + "";
    } else {
      var rest := "," + S.RenderClauses(cs[1..]);
      TakeClauseOfRender(cs[0], rest);
      assert S.RenderClauses(cs) == S.RenderClause(cs[0]) + rest;
      assert rest[1..] == S.RenderClauses(cs[1..]);
      ParseClausesOfRender(cs[1..]);
      assert [cs[0]] + cs[1..] == cs;
    }
  }

  lemma SymbolicStartsWithoutDigit(cs: seq<S.Clause>)
    requires |cs| > 0 && forall c :: c in cs ==> S.ClauseWellFormed(c)
    ensures |S.RenderClauses(cs)| > 0 && !P.IsOctalChar(S.RenderClauses(cs)[0])
  {
    var c := cs[0];
    assert S.ClauseWellFormed(c);
    TakeClauseOfRender(c, if |cs| == 1 then "" else "," + S.RenderClauses(cs[1..]));
    if |c.who| > 0 {
      WhoCharRoundTrip(c.who[0]);
      assert S.RenderClause(c)[0] == S.WhoChar(c.who[0]);
    } else {
      OpCharRoundTrip(c.actions[0].op);
      assert S.RenderClause(c)[0] == S.OpChar(c.actions[0].op);
    }
    assert S.RenderClauses(cs)[0] == S.RenderClause(c)[0];
  }

  lemma ParseModeOfRender(e: S.ModeExpr)
    requires S.WellFormed(e)
    ensures P.ParseMode(S.Render(e)) == P.Some(e)
  {
    match e
    case Absolute(ds) =>
      DigitCharRoundTrip(ds[0]);
      TakeDigitsOfRender(ds, "");
      assert S.Render(e) == S.RenderDigits(ds) + "";
    case Symbolic(cs) =>
      SymbolicStartsWithoutDigit(cs);
      ParseClausesOfRender(cs);
  }

  // ---------------------------------------------------------------------------
  // Soundness: what the parser returns renders back to its input
  // ---------------------------------------------------------------------------

  lemma TakeWhoRenders(s: string)
    ensures S.RenderWho(P.TakeWho(s).0) + P.TakeWho(s).1 == s
    decreases |s|
  {
    if |s| > 0 && P.IsWhoChar(s[0]) {
      WhoOfRoundTrip(s[0]);
      TakeWhoRenders(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma TakePermsRenders(s: string)
    ensures S.RenderPerms(P.TakePerms(s).0) + P.TakePerms(s).1 == s
    decreases |s|
  {
    if |s| > 0 && P.IsPermChar(s[0]) {
      PermOfRoundTrip(s[0]);
      TakePermsRenders(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma TakeDigitsRenders(s: string)
    ensures S.RenderDigits(P.TakeDigits(s).0) + P.TakeDigits(s).1 == s
    decreases |s|
  {
    if |s| > 0 && P.IsOctalChar(s[0]) {
      DigitOfRoundTrip(s[0]);
      TakeDigitsRenders(s[1..]);
      assert s == [s[0]] + s[1..];
    }
  }

  lemma TakeRhsRenders(s: string)
    ensures S.RenderRhs(P.TakeRhs(s).0) + P.TakeRhs(s).1 == s
  {
    if |s| > 0 && P.IsCopyChar(s[0]) {
      SrcOfRoundTrip(s[0]);
      assert s == [s[0]] + s[1..];
    } else if |s| > 0 && P.IsOctalChar(s[0]) {
      TakeDigitsRenders(s);
    } else {
      TakePermsRenders(s);
    }
  }

  lemma RenderActionsCons(a: S.Action, more: seq<S.Action>)
    ensures S.RenderActions([a] + more) == [S.OpChar(a.op)] + S.RenderRhs(a.rhs) + S.RenderActions(more)
  {
    assert ([a] + more)[0] == a && ([a] + more)[1..] == more;
  }

  lemma {:isolate_assertions} TakeActionsRenders(s: string)
    requires |s| > 0 && P.IsOpChar(s[0])
    ensures S.RenderActions(P.TakeActions(s).0) + P.TakeActions(s).1 == s
    decreases |s|
  {
    var rhs := P.TakeRhs(s[1..]);
    var a := S.Action(P.OpOf(s[0]), rhs.0);
    TakeRhsRenders(s[1..]);
    OpOfRoundTrip(s[0]);
    assert S.RenderRhs(rhs.0) + rhs.1 == s[1..];
    assert s == [s[0]] + s[1..];
    if |rhs.1| > 0 && P.IsOpChar(rhs.1[0]) {
      var more := P.TakeActions(rhs.1);
      assert P.TakeActions(s) == ([a] + more.0, more.1);
      TakeActionsRenders(rhs.1);
      RenderActionsCons(a, more.0);
      calc {
        S.RenderActions([a] + more.0) + more.1;
        [S.OpChar(a.op)] + S.RenderRhs(a.rhs) + S.RenderActions(more.0) + more.1;
        [s[0]] + (S.RenderRhs(rhs.0) + (S.RenderActions(more.0) + more.1));
        [s[0]] + (S.RenderRhs(rhs.0) + rhs.1);
        s;
      }
    } else {
      assert P.TakeActions(s) == ([a], rhs.1);
      RenderActionsCons(a, []);
      assert S.RenderActions([]) == [];
      calc {
        S.RenderActions([a]) + rhs.1;
        { assert [a] + [] == [a]; }
        [S.OpChar(a.op)] + S.RenderRhs(a.rhs) + S.RenderActions([]) + rhs.1;
        [s[0]] + (S.RenderRhs(rhs.0) + rhs.1);
        s;
      }
    }
  }

  lemma TakeClauseRenders(s: string)
    ensures P.TakeClause(s).Some? ==>
              S.RenderClause(P.TakeClause(s).value.0) + P.TakeClause(s).value.1 == s
  {
    var w := P.TakeWho(s);
    TakeWhoRenders(s);
    if |w.1| > 0 && P.IsOpChar(w.1[0]) {
      TakeActionsRenders(w.1);
    }
  }

  lemma ParseClausesRenders(s: string)
    ensures P.ParseClauses(s).Some? ==> S.RenderClauses(P.ParseClauses(s).value) == s
    decreases |s|
  {
    TakeClauseRenders(s);
    match P.TakeClause(s)
    case None =>
    case Some(cr) =>
      var (c, rest) := cr;
      if |rest| > 0 && rest[0] == ',' {
        ParseClausesRenders(rest[1..]);
        if P.ParseClauses(rest[1..]).Some? {
          var cs := P.ParseClauses(rest[1..]).value;
          assert P.ParseClauses(s).value == [c] + cs;
          assert ([c] + cs)[1..] == cs;
          assert rest == "," + rest[1..];
        }
      } else if |rest| == 0 {
        assert S.RenderClause(c) + rest == S.RenderClause(c);
      }
  }

  lemma ParseModeRenders(s: string)
    ensures P.ParseMode(s).Some? ==> S.Render(P.ParseMode(s).value) == s
  {
    if |s| > 0 && P.IsOctalChar(s[0]) {
      TakeDigitsRenders(s);
    } else {
      ParseClausesRenders(s);
    }
  }

  // ---------------------------------------------------------------------------
  // What the rest of the proof uses
  // ---------------------------------------------------------------------------

  lemma ParseNoneIsInvalid(s: string)
    requires P.ParseMode(s) == P.None
    ensures S.ModeInvalid(s)
  {
    forall e | S.WellFormed(e)
      ensures S.Render(e) != s
    {
      ParseModeOfRender(e);
    }
  }

  lemma ParseSomeDenotes(s: string, umask: bv32)
    requires P.ParseMode(s).Some?
    ensures S.ModeDenotes(s, umask, S.Meaning(P.ParseMode(s).value, umask))
  {
    ParseModeRenders(s);
  }

  // A valid MODE has exactly one meaning.
  lemma MeaningUnique(s: string, umask: bv32, m1: bv32, m2: bv32)
    requires S.ModeDenotes(s, umask, m1) && S.ModeDenotes(s, umask, m2)
    ensures m1 == m2
  {
    var e1 :| S.WellFormed(e1) && S.Render(e1) == s && m1 == S.Meaning(e1, umask);
    var e2 :| S.WellFormed(e2) && S.Render(e2) == s && m2 == S.Meaning(e2, umask);
    ParseModeOfRender(e1);
    ParseModeOfRender(e2);
  }
}
