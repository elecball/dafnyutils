include "../Spec/RealpathSpec.dfy"
include "../Proof/RealpathPathProof.dfy"

module RealpathCore {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import E = Errnos
  import R = Results
  import S = RealpathSchema
  import Spec = RealpathSpec
  import Utf8 = Utf8Semantics
  import SE = StringEscaping
  import CliTypes
  import PathProof = RealpathPathProof

  lemma JoinSnoc(parts: seq<string>, name: string)
    ensures BW.JoinSegments(parts + [name]) ==
            (if parts == [] then name else BW.JoinSegments(parts) + "/" + name)
    decreases |parts|
  {
    if |parts| > 1 {
      JoinSnoc(parts[1..], name);
      assert (parts + [name])[1..] == parts[1..] + [name];
      assert (parts + [name])[0] == parts[0];
      reveal BW.JoinSegments();
      calc {
         BW.JoinSegments(parts + [name]);
      == parts[0] + "/" + BW.JoinSegments(parts[1..] + [name]);
      == parts[0] + "/" + (BW.JoinSegments(parts[1..]) + "/" + name);
      == BW.JoinSegments(parts) + "/" + name;
      }
    }
  }

  method BuildExpression(text: string, anchor: string) returns (expr: S.PathExpr)
    ensures Spec.Origin(expr) == anchor
    ensures BW.JoinSegments(Spec.Components(expr)) == text
    ensures forall name | name in Spec.Components(expr) :: '/' !in name
  {
    expr := S.Anchor(anchor);
    var start, i := 0, 0;
    while i < |text|
      invariant 0 <= start <= i <= |text|
      invariant Spec.Origin(expr) == anchor
      invariant forall name | name in Spec.Components(expr) :: '/' !in name
      invariant '/' !in text[start..i]
      invariant BW.JoinSegments(Spec.Components(expr)) +
                (if Spec.Components(expr) == [] then "" else "/") + text[start..i] == text[..i]
      decreases |text| - i
    {
      if text[i] == '/' {
        ghost var previous := Spec.Components(expr);
        JoinSnoc(previous, text[start..i]);
        expr := S.Child(expr, text[start..i]);
        start := i + 1;
      }
      i := i + 1;
    }
    JoinSnoc(Spec.Components(expr), text[start..]);
    expr := S.Child(expr, text[start..]);
  }

  method ParsePath(path: string, cwd: string) returns (expr: S.PathExpr)
    ensures Spec.Syntax(path, cwd, expr)
  {
    expr := BuildExpression(if BW.IsAbsolutePath(path) then path[1..] else path,
                            if BW.IsAbsolutePath(path) then "/" else cwd);
  }

  method Parent(path: string) returns (parent: string)
    ensures Spec.ParentPath(path, parent)
  {
    var i := |path|;
    while i > 0 && path[i - 1] != '/'
      invariant 0 <= i <= |path|
      invariant forall j: nat | i <= j < |path| :: path[j] != '/'
      decreases i
    {
      i := i - 1;
    }
    if i <= 1 { parent := "/"; }
    else { parent := path[..i - 1]; }
    if i == 0 {
      assert '/' !in path;
    } else {
      assert exists cut: nat ::
          cut < |path| && path[cut] == '/' &&
          (forall j: nat | cut < j < |path| :: path[j] != '/') &&
          parent == (if cut == 0 then "/" else path[..cut]);
    }
  }

  method NeedsDirectory(suffix: string) returns (needed: bool)
    ensures needed == Spec.DirectorySuffix(suffix)
  {
    if suffix == "" || suffix[0] != '/' { return false; }
    var parts := BW.SplitSegments(suffix, 0, 0);
    var i := 0;
    while i < |parts| && parts[i] == "."
      invariant 0 <= i <= |parts|
      invariant forall j: nat | j < i :: parts[j] == "."
      decreases |parts| - i
    { i := i + 1; }
    needed := i == |parts| || parts[i] == "..";
    if !needed {
      assert forall j: nat | j < |parts| && parts[j] == ".." ::
          !(forall k: nat | k < j :: parts[k] == ".") by {
        forall j: nat | j < |parts| && parts[j] == ".."
          ensures !(forall k: nat | k < j :: parts[k] == ".")
        {
          if j < i { assert parts[j] == "."; }
          else if j > i { assert parts[i] != "."; }
        }
      }
    }
  }

  method ObserveStatus(io: BenchIO.IO, path: string) returns (status: Spec.Status)
    ensures Spec.StatusObservation(io.fs(), io.trustedNativeFailures(), path, status)
  {
    var result := io.IsDirectory(path, true);
    status := Spec.ObservedStatus(result.Ok?, C.ResultValue(result, false), C.ResultErrno(result));
  }

  method InterpretStrip(expr: S.PathExpr, existence: S.Existence,
                        suffix: string, io: BenchIO.IO)
    returns (result: Spec.PathResult, ghost proof: Spec.MeaningProof)
    ensures Spec.Meaning(io.fs(), io.trustedNativeFailures(), existence,
                         expr, suffix, result, proof)
    decreases expr
  {
    hide *;
    if expr.Anchor? {
      PathProof.Directory(io.fs(), io.trustedNativeFailures(), existence, expr.directory, suffix);
      return Spec.Ok(expr.directory), Spec.DirectoryMeaning;
    }
    var parent, prior := InterpretStrip(expr.parent, existence, "/" + expr.name + suffix, io);
    ghost var rule := Spec.SameDirectory;
    if !parent.Ok? {
      result := parent;
      rule := Spec.InheritedFailure;
      PathProof.Failure(io.fs(), io.trustedNativeFailures(), existence, parent, expr.name, suffix);
    } else if expr.name == "" || expr.name == "." {
      result := parent;
      PathProof.Same(io.fs(), io.trustedNativeFailures(), existence, parent, expr.name, suffix);
    } else if expr.name == ".." {
      var value := Parent(parent.v);
      result := Spec.Ok(value);
      rule := Spec.ParentDirectory;
      PathProof.Up(io.fs(), io.trustedNativeFailures(), existence, parent.v, expr.name, suffix, value);
    } else {
      var status;
      result, status := Ordinary(parent.v, expr.name, existence, suffix, io);
      rule := Spec.Ordinary(status);
      PathProof.Name(io.fs(), io.trustedNativeFailures(), existence,
                     parent.v, expr.name, suffix, result, status);
    }
    PathProof.Child(io.fs(), io.trustedNativeFailures(), existence, expr.parent,
                    expr.name, suffix, parent, result, prior, rule);
    proof := Spec.ChildMeaning(prior, parent, rule);
  }

  method Ordinary(parent: string, name: string, existence: S.Existence,
                  suffix: string, io: BenchIO.IO)
    returns (result: Spec.PathResult, status: Spec.Status)
    ensures Spec.OrdinaryMeaning(io.fs(), io.trustedNativeFailures(), existence,
                                 parent, name, suffix, result, status)
  {
    var path := Spec.ChildPath(parent, name);
    var needsDirectory := NeedsDirectory(suffix);
    status := Spec.NoStatus;
    if existence != S.Missing && (needsDirectory || suffix == "") {
      status := ObserveStatus(io, if needsDirectory then path + "/" else path);
    }
    var error := 0;
    if existence != S.Missing {
      if needsDirectory {
        if !status.ok &&
           !(existence == S.AllButLast && status.err == E.ENOENT && Spec.Slashes(suffix)) {
          error := status.err;
        }
      } else if suffix == "" && !status.ok &&
                !(existence == S.AllButLast && status.err == E.ENOENT) {
        error := status.err;
      }
    }
    result := if error == 0 then Spec.Ok(path) else Spec.Err(error);
  }

  ghost function Depth(expr: S.PathExpr): nat
    decreases expr
  {
    match expr
    case Anchor(_) => 0
    case Child(parent, _) => Depth(parent) + 1
  }

  method InterpretPhysical(expr: S.PathExpr, existence: S.Existence,
                           suffix: string, before: Spec.History, io: BenchIO.IO)
    returns (result: Spec.PathResult, after: Spec.History, ghost proof: Spec.PhysicalProof)
    requires Spec.ValidHistory(before)
    modifies io.statusObservationsRegion
    ensures Spec.ValidHistory(after) && Spec.Extends(before, after)
    ensures old(io.statusCursor()) <= io.statusCursor()
    ensures Spec.PhysicalMeaning(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                 old(io.statusCursor()), io.statusCursor(), existence, expr, suffix, before, after, result, proof)
    decreases 20 - before.warm, Spec.NativeRecordCapacity - |before.seen|, Depth(expr), 1
  {
    hide *;
    reveal Spec.ValidHistory(), Spec.Extends(), Depth();
    ghost var first := io.statusCursor();
    if expr.Anchor? {
      PathProof.PhysicalDirectory(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                  first, existence, expr.directory, suffix, before);
      return Spec.Ok(expr.directory), before, Spec.PhysicalDirectory;
    }
    var parent, parentHistory, prior :=
      InterpretPhysical(expr.parent, existence, "/" + expr.name + suffix, before, io);
    ghost var middle := io.statusCursor();
    assert before.seen <= parentHistory.seen;
    PathProof.SetCardinality(before.seen, parentHistory.seen);
    ghost var rule;
    result, after, rule := PhysicalComponent(parent, expr.name, existence, suffix,
                                             parentHistory, Depth(expr), io);
    PathProof.PhysicalChild(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                            first, middle, io.statusCursor(), existence, expr.parent, expr.name, suffix,
                            before, parentHistory, after, parent, result, prior, rule);
    proof := Spec.PhysicalChild(prior, parent, parentHistory, middle, rule);
  }

  method PhysicalComponent(parent: Spec.PathResult, name: string, existence: S.Existence,
                           suffix: string, before: Spec.History, ghost depth: nat, io: BenchIO.IO)
    returns (result: Spec.PathResult, after: Spec.History, ghost rule: Spec.PhysicalRule)
    requires Spec.ValidHistory(before)
    modifies io.statusObservationsRegion
    ensures Spec.ValidHistory(after) && Spec.Extends(before, after)
    ensures old(io.statusCursor()) <= io.statusCursor()
    ensures Spec.PhysicalComponent(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                   old(io.statusCursor()), io.statusCursor(), existence, parent, name, suffix, before, after, result, rule)
    decreases 20 - before.warm, Spec.NativeRecordCapacity - |before.seen|, depth, 0
  {
    hide *;
    reveal Spec.PhysicalComponent(), Spec.ValidHistory(), Spec.Extends();
    ghost var first := io.statusCursor();
    after := before;
    if !parent.Ok? { return parent, after, Spec.PhysicalFailure; }
    if name == "" || name == "." { return parent, after, Spec.PhysicalSame; }
    if name == ".." {
      var value := Parent(parent.v);
      return Spec.Ok(value), after, Spec.PhysicalParent;
    }
    var path := Spec.ChildPath(parent.v, name);
    var read := io.ReadLink(path);
    if read.Err? {
      var status := Spec.NoStatus;
      var needsDirectory := NeedsDirectory(suffix);
      if existence != S.Missing && needsDirectory { status := ObserveStatus(io, path + "/"); }
      var error := 0;
      if existence != S.Missing {
        if needsDirectory {
          if !status.ok && !(existence == S.AllButLast && status.err == E.ENOENT && Spec.Slashes(suffix)) {
            error := status.err;
          }
        } else {
          error := C.ResultErrno(read);
          if error == E.EINVAL ||
             (existence == S.AllButLast && error == E.ENOENT && Spec.Slashes(suffix)) { error := 0; }
        }
      }
      result := if error == 0 then Spec.Ok(path) else Spec.Err(error);
      reveal Spec.PhysicalOrdinaryMeaning(), Spec.EntryStatus();
      assert error == (if result.Err? then result.e else 0);
      assert Spec.EntryStatus(io.fs(), io.trustedNativeFailures(), path, suffix, status);
      assert Spec.PhysicalOrdinaryMeaning(io.fs(), io.trustedNativeFailures(), existence,
                                          parent.v, name, suffix, result, read, status);
      return result, after, Spec.PhysicalOrdinary(read, status);
    }
    var status := Spec.NoParentStatus;
    if before.warm == 20 {
      var observed := io.GetFileStatus(Spec.ChildPath(parent.v, ""), true);
      status := Spec.ParentStatus(observed);
    }
    ghost var middle := io.statusCursor();
    assert Spec.ParentQuery(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                            first, middle, parent.v, before, status) by { reveal Spec.ParentQuery(); }
    if status.ParentStatus? && status.result.Err? {
      return Spec.Err(C.ResultErrno(status.result)), after, Spec.PhysicalParentFailure(read.v, status);
    }
    var key := Spec.ParentKey(status, name + suffix);
    reveal Spec.Repeated(), Spec.Full();
    if Spec.Repeated(before, key) {
      result := if existence == S.Missing then Spec.Ok(path) else Spec.Err(E.ELOOP);
      return result, after, Spec.PhysicalRepeat(read.v, status);
    }
    if Spec.Full(before) { return Spec.MemoryFatal, after, Spec.PhysicalMemory(read.v, status); }
    var next := Spec.Added(before, key);
    reveal Spec.Added();
    assert Spec.ValidHistory(next) && Spec.Extends(before, next);
    var expr := ParsePath(read.v, parent.v);
    ghost var proof;
    result, after, proof := InterpretPhysical(expr, existence, suffix, next, io);
    rule := Spec.PhysicalFollow(read.v, status, expr, proof);
  }

  method PhysicalCanonicalize(existence: S.Existence, cwd: string, path: string, io: BenchIO.IO)
    returns (result: Spec.PathResult)
    modifies io.statusObservationsRegion
    ensures Spec.PhysicalCanonicalizes(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                       old(io.statusCursor()), io.statusCursor(), existence, cwd, path, result)
  {
    hide *;
    var expr := ParsePath(path, cwd);
    ghost var first := io.statusCursor();
    var after;
    ghost var proof;
    assert Spec.ValidHistory(Spec.History(0, {})) by { reveal Spec.ValidHistory(); }
    result, after, proof := InterpretPhysical(expr, existence, "", Spec.History(0, {}), io);
    reveal Spec.PhysicalCanonicalizes();
  }

  method Canonicalize(raw: S.RealpathCmdRaw, cwd: BW.IOResult<string>,
                                                              path: string, io: BenchIO.IO) returns (result: Spec.PathResult)
    modifies io.statusObservationsRegion
    ensures Spec.Canonicalizes(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                               old(io.statusCursor()), io.statusCursor(), raw, cwd, path, result)
  {
    hide *;
    reveal Spec.Canonicalizes();
    if path == "" { return Spec.Err(E.ENOENT); }
    if !BW.IsAbsolutePath(path) && cwd.Err? {
      return if C.ResultErrno(cwd) == E.ENOMEM then Spec.MemoryFatal else Spec.Err(C.ResultErrno(cwd));
    }
    if raw.links == S.Physical {
      result := PhysicalCanonicalize(raw.existence, if cwd.Ok? then cwd.v else "/", path, io);
      return;
    }
    var expr := ParsePath(path, if cwd.Ok? then cwd.v else "/");
    ghost var proof;
    var prior;
    prior, proof := InterpretStrip(expr, raw.existence, "", io);
    if raw.links == S.Strip || !prior.Ok? { result := prior; }
    else { result := PhysicalCanonicalize(raw.existence, "/", prior.v, io); }
  }

  method Relative(from: string, target: string) returns (value: string)
    ensures Spec.RelativePath(from, target, value)
  {
    var left := BW.SplitSegments(from, 0, 0);
    var right := BW.SplitSegments(target, 0, 0);
    var common := 0;
    while common < |left| && common < |right| && left[common] == right[common]
      invariant 0 <= common <= |left| && common <= |right|
      invariant left[..common] == right[..common]
      decreases |left| - common
    { common := common + 1; }
    var components := seq(|left| - common, i => "..") + right[common..];
    value := if components == [] then "." else BW.JoinSegments(components);
    assert Spec.LongestCommonPrefix(left, right, common);
  }
  method PrepareDirectory(raw: S.RealpathCmdRaw, cwd: BW.IOResult<string>, operand: string,
                                                                  io: BenchIO.IO) returns (result: Spec.DirectoryResult, ghost evidence: Spec.DirectoryEvidence)
    modifies io.statusObservationsRegion
    ensures Spec.DirectoryPreparation(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                      old(io.statusCursor()), io.statusCursor(), raw, cwd, operand, evidence) && evidence.result == result
  {
    var canonical := Canonicalize(raw, cwd, operand, io);
    var status := Spec.NoStatus;
    if canonical.MemoryFatal? { result := Spec.DirectoryMemory; }
    else if canonical.Err? { result := Spec.DirectoryFailure(operand, canonical.e, false); }
    else if raw.existence != S.Existing { result := Spec.DirectoryReady(canonical.v); }
    else {
      status := ObserveStatus(io, canonical.v);
      if !status.ok { result := Spec.DirectoryFailure(canonical.v, status.err, true); }
      else if !status.directory { result := Spec.DirectoryFailure(operand, E.ENOTDIR, false); }
      else { result := Spec.DirectoryReady(canonical.v); }
    }
    evidence := Spec.DirectoryEvidence(canonical, status, result);
  }

  method PrepareRelative(raw: S.RealpathCmdRaw, cwd: BW.IOResult<string>, io: BenchIO.IO)
    returns (setup: Spec.Setup, ghost evidence: Spec.RelativeEvidence)
    modifies io.statusObservationsRegion
    ensures Spec.RelativeSetup(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                               old(io.statusCursor()), io.statusCursor(), raw, cwd, setup, evidence)
  {
    hide *;
    reveal Spec.RelativeSetup(), Spec.ToOperand(), Spec.SetupFailure();
    ghost var empty := Spec.DirectoryEvidence(Spec.Ok("/"), Spec.NoStatus, Spec.DirectoryReady("/"));
    evidence := Spec.RelativeEvidence(empty, empty, io.statusCursor());
    var requested := Spec.ToOperand(raw);
    if requested.None? { return Spec.RelativeReady(CliTypes.None, CliTypes.None), evidence; }
    var relativeTo, toEvidence := PrepareDirectory(raw, cwd, requested.value, io);
    evidence := Spec.RelativeEvidence(toEvidence, empty, io.statusCursor());
    if !relativeTo.DirectoryReady? { return Spec.SetupFailure(relativeTo), evidence; }
    if raw.relativeBase.None? {
      return Spec.RelativeReady(CliTypes.Some(relativeTo.path), CliTypes.None), evidence;
    }
    if raw.relativeTo.None? {
      return Spec.RelativeReady(CliTypes.Some(relativeTo.path), CliTypes.Some(relativeTo.path)), evidence;
    }
    ghost var cursor := io.statusCursor();
    var relativeBase, baseEvidence := PrepareDirectory(raw, cwd, raw.relativeBase.value, io);
    evidence := Spec.RelativeEvidence(toEvidence, baseEvidence, cursor);
    if !relativeBase.DirectoryReady? { return Spec.SetupFailure(relativeBase), evidence; }
    setup := if Spec.PathPrefix(relativeBase.path, relativeTo.path) then
      Spec.RelativeReady(CliTypes.Some(relativeTo.path), CliTypes.Some(relativeBase.path))
    else Spec.RelativeReady(CliTypes.None, CliTypes.None);
  }

  method Render(setup: Spec.Setup, path: string) returns (value: string)
    requires setup.RelativeReady?
    ensures Spec.OutputPath(setup, path, value)
  {
    if setup.relativeTo.Some? &&
       (setup.relativeBase.None? || Spec.PathPrefix(setup.relativeBase.value, path)) {
      value := Relative(setup.relativeTo.value, path);
    } else { value := path; }
  }

  method Operand(raw: S.RealpathCmdRaw, cwd: BW.IOResult<string>, setup: Spec.Setup,
                                                         path: string, io: BenchIO.IO)
    returns (result: Spec.PathResult, output: BW.Bytes, diagnostics: BW.Bytes)
    requires setup.RelativeReady?
    modifies io.statusObservationsRegion
    ensures Spec.OperandPiece(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                              old(io.statusCursor()), io.statusCursor(), raw, cwd, setup, path, result, output, diagnostics)
  {
    result := Canonicalize(raw, cwd, path, io);
    output, diagnostics := [], [];
    if result.MemoryFatal? { diagnostics := Spec.MemoryMessage(); }
    else if result.Err? {
      if !raw.quiet {
        var reason := io.GetCLocaleErrnoText(result.e);
        diagnostics := Spec.ErrorMessage(path, reason);
      }
    } else {
      var value := Render(setup, result.v);
      output := Utf8.Encode(value) + Spec.Delimiter(raw);
    }
  }

  lemma PartitionAppend(pieces: seq<BW.Bytes>, output: BW.Bytes, cuts: seq<nat>, piece: BW.Bytes)
    requires Spec.Partition(pieces, output, cuts)
    ensures Spec.Partition(pieces + [piece], output + piece, cuts + [|output + piece|])
  {
    forall i: nat {:trigger (cuts + [|output + piece|])[i]} | i < |pieces| + 1
      ensures (cuts + [|output + piece|])[i] <=
              (cuts + [|output + piece|])[i + 1] <= |output + piece|
      ensures (output + piece)[(cuts + [|output + piece|])[i]..
              (cuts + [|output + piece|])[i + 1]] == (pieces + [piece])[i]
    {
      if i < |pieces| { assert cuts[i + 1] <= |output|; }
    }
  }

  lemma FailureAppend(results: seq<Spec.PathResult>, result: Spec.PathResult)
    ensures (exists j: nat :: j < |results + [result]| && !(results + [result])[j].Ok?) <==>
            ((exists j: nat :: j < |results| && !results[j].Ok?) || !result.Ok?)
  {
    if exists j: nat :: j < |results| && !results[j].Ok? {
      var j: nat :| j < |results| && !results[j].Ok?;
      assert !(results + [result])[j].Ok?;
    }
    if !result.Ok? { assert !(results + [result])[|results|].Ok?; }
    if exists j: nat :: j < |results + [result]| && !(results + [result])[j].Ok? {
      var j: nat :| j < |results + [result]| && !(results + [result])[j].Ok?;
      if j < |results| { assert !results[j].Ok?; }
      else { assert j == |results| && !result.Ok?; }
    }
  }

  method Operands(raw: S.RealpathCmdRaw, cwd: BW.IOResult<string>, setup: Spec.Setup, io: BenchIO.IO)
    returns (output: BW.Bytes, diagnostics: BW.Bytes, exit: int, ghost evidence: Spec.OperandEvidence)
    requires setup.RelativeReady?
    modifies io.statusObservationsRegion
    ensures Spec.Operands(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                          old(io.statusCursor()), io.statusCursor(), raw, cwd, setup, raw.operands, output, diagnostics, exit, evidence)
  {
    hide *;
    ghost var first := io.statusCursor();
    output, diagnostics, exit := [], [], 0;
    ghost var results: seq<Spec.PathResult> := [];
    ghost var outputs: seq<BW.Bytes> := [];
    ghost var errors: seq<BW.Bytes> := [];
    ghost var outCuts: seq<nat> := [0];
    ghost var errCuts: seq<nat> := [0];
    ghost var statusCuts: seq<nat> := [first];
    var i := 0;
    var fatal := false;
    assert Spec.Partition([], [], [0]) by { reveal Spec.Partition(); }
    while i < |raw.operands| && !fatal
      invariant 0 <= i <= |raw.operands|
      invariant |results| == i && |outputs| == i && |errors| == i
      invariant |statusCuts| == i + 1 && statusCuts[0] == first && statusCuts[i] == io.statusCursor()
      invariant Spec.Partition(outputs, output, outCuts) && Spec.Partition(errors, diagnostics, errCuts)
      invariant forall j: nat | j < i :: Spec.OperandPiece(io.fs(), io.trustedNativeFailures(), io.statusObservations(),
                                                           statusCuts[j], statusCuts[j + 1], raw, cwd, setup, raw.operands[j], results[j], outputs[j], errors[j])
      invariant forall j: nat | j + 1 < i :: !results[j].MemoryFatal?
      invariant fatal <==> i > 0 && results[i - 1].MemoryFatal?
      invariant exit == (if exists j: nat :: j < i && !results[j].Ok? then 1 else 0)
      decreases |raw.operands| - i
    {
      var result, out, err := Operand(raw, cwd, setup, raw.operands[i], io);
      PartitionAppend(outputs, output, outCuts, out);
      PartitionAppend(errors, diagnostics, errCuts, err);
      output, diagnostics := output + out, diagnostics + err;
      outputs, errors := outputs + [out], errors + [err];
      outCuts, errCuts := outCuts + [|output|], errCuts + [|diagnostics|];
      FailureAppend(results, result);
      results := results + [result];
      statusCuts := statusCuts + [io.statusCursor()];
      if !result.Ok? { exit := 1; }
      fatal := result.MemoryFatal?;
      i := i + 1;
    }
    evidence := Spec.OperandEvidence(results, outputs, errors, outCuts, errCuts, statusCuts);
    reveal Spec.Operands();
  }

  method Prepare(raw: S.RealpathCmdRaw, io: BenchIO.IO)
    returns (output: BW.Bytes, diagnostics: BW.Bytes, exit: int, ghost evidence: Spec.Preparation)
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures Spec.Prepared(raw, io, output, diagnostics, exit, evidence)
  {
    hide *;
    reveal Spec.Prepared();
    evidence := Spec.EarlyPreparation;
    if raw.mode == S.Help { return Spec.HelpText(), [], 0, evidence; }
    if raw.mode == S.Version { return Spec.VersionText(), [], 0, evidence; }
    if raw.operands == [] { return [], Spec.MissingOperand(), 1, evidence; }
    var cwd := io.GetCwd();
    assert Spec.CwdObservation(io, cwd) by { reveal Spec.CwdObservation(); }
    var setup, relative := PrepareRelative(raw, cwd, io);
    ghost var cursor := io.statusCursor();
    ghost var operands := Spec.OperandEvidence([], [], [], [0], [0], [cursor]);
    if setup.RelativeMemory? { output, diagnostics, exit := [], Spec.MemoryMessage(), 1; }
    else if setup.RelativeFailure? {
      var reason := io.GetCLocaleErrnoText(setup.error);
      output, diagnostics, exit := [], Spec.SetupError(setup, reason), 1;
    } else {
      output, diagnostics, exit, operands := Operands(raw, cwd, setup, io);
    }
    evidence := Spec.RunPreparation(cwd, setup, relative, operands, cursor);
  }

  method Emit(io: BenchIO.IO, output: BW.Bytes, diagnostics: BW.Bytes, normalExit: int)
    returns (exit: int, committed: nat, outError: int, errCommitted: nat, errError: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionOutcome(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                 io.trustedStreams(), output, diagnostics, normalExit, exit,
                                 committed, outError, errCommitted, errError)
  {
    hide *;
    committed, outError, errCommitted, errError := 0, 0, 0, 0;
    if output != [] {
      var written := io.WriteStdout(output);
      committed, outError := C.WriteResultCommitted(written), C.ResultErrno(written);
      assert C.WriteStdoutSpec(old(io.stdout()), io.trustedStreams(), io.stdout(),
                               output, committed, outError);
    }
    var errors := diagnostics;
    if outError != 0 {
      var reason := io.GetCLocaleErrnoText(outError);
      reveal C.GetCLocaleErrnoTextSpec();
      errors := errors + Spec.WriteError(reason);
    }
    assert errors == diagnostics +
                     (if outError == 0 then [] else Spec.WriteError(C.CLocaleErrnoTextResult(outError)));
    if errors != [] {
      var written := io.WriteStderr(errors);
      errCommitted, errError := C.WriteResultCommitted(written), C.ResultErrno(written);
      assert C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                               errors, errCommitted, errError);
    }
    exit := if outError != 0 || errError != 0 then 1 else normalExit;
    reveal Spec.EmissionOutcome();
  }

  twostate predicate CoreSummary(raw: S.RealpathCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.directoryStateRegion, io.fsRegion,
          io.cwdRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion,
          io.trustedStreamsRegion
  {
    exists output: BW.Bytes, diagnostics: BW.Bytes, normalExit: int, evidence: Spec.Preparation,
      committed: nat, outError: int, errCommitted: nat, errError: int ::
      Spec.Prepared(raw, io, output, diagnostics, normalExit, evidence) &&
      Spec.EmissionOutcome(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                           io.trustedStreams(), output, diagnostics, normalExit, exit,
                           committed, outError, errCommitted, errError)
  }

  method RunCore(raw: S.RealpathCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.directoryStateRegion, io.statusObservationsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    hide *;
    var output, diagnostics, normalExit, evidence := Prepare(raw, io);
    var committed, outError, errCommitted, errError;
    exit, committed, outError, errCommitted, errError := Emit(io, output, diagnostics, normalExit);
    assert Spec.Prepared(raw, io, output, diagnostics, normalExit, evidence);
    assert Spec.EmissionOutcome(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit,
                                committed, outError, errCommitted, errError);
    reveal CoreSummary();
  }
}
