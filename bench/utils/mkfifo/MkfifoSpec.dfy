include "MkfifoSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "CliSupport.dfy"

// Observable behavior of GNU mkfifo (coreutils src/mkfifo.c at
// 2cf491412c199e2211880ec3f4ba387026638a33). MODE follows gnulib
// lib/modechange.c (mode_compile, mode_adjust) at
// 83730551b451b43577531986a5c4300e0166c42f, as mkfifo uses it:
// mode_adjust (0666, false, umask, changes).
//
// A MODE string is valid iff some well-formed expression renders to it; its
// result is that expression's Meaning. No parsing algorithm appears here.
module MkfifoSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = MkfifoSchema
  import Utf8 = Utf8Semantics
  import CliModel
  import C = IOContract

  // ===========================================================================
  // MODE: abstract syntax, Render, Meaning
  // ===========================================================================


  // ---------------------------------------------------------------------------
  // Abstract syntax
  // ---------------------------------------------------------------------------

  datatype Who = WhoU | WhoG | WhoO | WhoA
  datatype OpSym = OpAdd | OpRemove | OpSet
  datatype Perm = PermR | PermW | PermX | PermCondX | PermS | PermT
  datatype CopySrc = FromU | FromG | FromO

  type OctDigit = d: nat | d < 8

  // The right-hand side of one operator.
  datatype Rhs =
    | Perms(perms: seq<Perm>)        // [rwxXst]*, possibly empty
    | Copy(src: CopySrc)             // u | g | o: copy that class's current bits
    | Octal(digits: seq<OctDigit>)   // [0-7]+ after an operator

  datatype Action = Action(op: OpSym, rhs: Rhs)

  // [ugoa]* followed by one or more actions.
  datatype Clause = Clause(who: seq<Who>, actions: seq<Action>)

  datatype ModeExpr =
    | Absolute(digits: seq<OctDigit>)  // the whole string is an octal number
    | Symbolic(clauses: seq<Clause>)   // clauses separated by ','

  // ---------------------------------------------------------------------------
  // Well-formedness
  // ---------------------------------------------------------------------------

  const ALLM: nat := 4095 // 07777

  function OctalValue(ds: seq<OctDigit>): nat
    decreases |ds|
  {
    if |ds| == 0 then 0 else OctalValue(ds[..|ds| - 1]) * 8 + ds[|ds| - 1]
  }

  // An octal right-hand side needs an empty who list, a value of at most 07777,
  // and must end its clause (GNU requires ',' or the end right after the digits).
  predicate ActionWellFormed(who: seq<Who>, a: Action, isLast: bool)
  {
    match a.rhs
    case Octal(ds) => |ds| > 0 && OctalValue(ds) <= ALLM && |who| == 0 && isLast
    case _ => true
  }

  predicate ClauseWellFormed(c: Clause)
  {
    |c.actions| > 0 &&
    forall i :: 0 <= i < |c.actions| ==>
                  ActionWellFormed(c.who, c.actions[i], i == |c.actions| - 1)
  }

  predicate WellFormed(e: ModeExpr)
  {
    match e
    case Absolute(ds) => |ds| > 0 && OctalValue(ds) <= ALLM
    case Symbolic(cs) => |cs| > 0 && forall c :: c in cs ==> ClauseWellFormed(c)
  }

  // ---------------------------------------------------------------------------
  // Concrete syntax: Render
  // ---------------------------------------------------------------------------

  function WhoChar(w: Who): char
  {
    match w
    case WhoU => 'u'
    case WhoG => 'g'
    case WhoO => 'o'
    case WhoA => 'a'
  }

  function OpChar(o: OpSym): char
  {
    match o
    case OpAdd => '+'
    case OpRemove => '-'
    case OpSet => '='
  }

  function PermChar(p: Perm): char
  {
    match p
    case PermR => 'r'
    case PermW => 'w'
    case PermX => 'x'
    case PermCondX => 'X'
    case PermS => 's'
    case PermT => 't'
  }

  function SrcChar(s: CopySrc): char
  {
    match s
    case FromU => 'u'
    case FromG => 'g'
    case FromO => 'o'
  }

  function DigitChar(d: OctDigit): char
  {
    ('0' as int + d) as char
  }

  function RenderWho(ws: seq<Who>): string
    decreases |ws|
  {
    if |ws| == 0 then "" else [WhoChar(ws[0])] + RenderWho(ws[1..])
  }

  function RenderPerms(ps: seq<Perm>): string
    decreases |ps|
  {
    if |ps| == 0 then "" else [PermChar(ps[0])] + RenderPerms(ps[1..])
  }

  function RenderDigits(ds: seq<OctDigit>): string
    decreases |ds|
  {
    if |ds| == 0 then "" else [DigitChar(ds[0])] + RenderDigits(ds[1..])
  }

  function RenderRhs(r: Rhs): string
  {
    match r
    case Perms(ps) => RenderPerms(ps)
    case Copy(src) => [SrcChar(src)]
    case Octal(ds) => RenderDigits(ds)
  }

  function RenderActions(as_: seq<Action>): string
    decreases |as_|
  {
    if |as_| == 0 then ""
    else [OpChar(as_[0].op)] + RenderRhs(as_[0].rhs) + RenderActions(as_[1..])
  }

  function RenderClause(c: Clause): string
  {
    RenderWho(c.who) + RenderActions(c.actions)
  }

  function RenderClauses(cs: seq<Clause>): string
    decreases |cs|
  {
    if |cs| == 0 then ""
    else if |cs| == 1 then RenderClause(cs[0])
    else RenderClause(cs[0]) + "," + RenderClauses(cs[1..])
  }

  function Render(e: ModeExpr): string
  {
    match e
    case Absolute(ds) => RenderDigits(ds)
    case Symbolic(cs) => RenderClauses(cs)
  }

  // ---------------------------------------------------------------------------
  // Meaning
  // ---------------------------------------------------------------------------

  const S_ISUID: bv32 := 0x800
  const S_ISGID: bv32 := 0x400
  const S_ISVTX: bv32 := 0x200
  const S_IRWXU: bv32 := 0x1C0
  const S_IRWXG: bv32 := 0x038
  const S_IRWXO: bv32 := 0x007
  const READ_BITS: bv32 := 0x124   // 0444
  const WRITE_BITS: bv32 := 0x092  // 0222
  const EXEC_BITS: bv32 := 0x049   // 0111
  const PERMISSION_BITS: bv32 := 0x1FF  // 0777
  const MODE_BITS: bv32 := 0xFFF        // 07777
  const MKFIFO_BASE_MODE: bv32 := 0x1B6 // 0666 = a=rw

  function WhoMask(w: Who): bv32
  {
    match w
    case WhoU => S_ISUID | S_IRWXU
    case WhoG => S_ISGID | S_IRWXG
    case WhoO => S_ISVTX | S_IRWXO
    case WhoA => MODE_BITS
  }

  // Bits selected by the who list; 0 means "no who given".
  function WhoBits(ws: seq<Who>): bv32
    decreases |ws|
  {
    if |ws| == 0 then 0 else WhoMask(ws[0]) | WhoBits(ws[1..])
  }

  function PermBits(p: Perm): bv32
  {
    match p
    case PermR => READ_BITS
    case PermW => WRITE_BITS
    case PermX => EXEC_BITS
    case PermCondX => 0
    case PermS => S_ISUID | S_ISGID
    case PermT => S_ISVTX
  }

  function PermsBits(ps: seq<Perm>): bv32
    decreases |ps|
  {
    if |ps| == 0 then 0 else PermBits(ps[0]) | PermsBits(ps[1..])
  }

  function SrcBits(s: CopySrc): bv32
  {
    match s
    case FromU => S_IRWXU
    case FromG => S_IRWXG
    case FromO => S_IRWXO
  }

  // Copy: take the source class's current bits and repeat each kind (r, w, x)
  // in all three classes.
  function CopyBits(s: CopySrc, cur: bv32): bv32
  {
    var v := SrcBits(s) & cur;
    v
    | (if v & READ_BITS != 0 then READ_BITS else 0)
    | (if v & WRITE_BITS != 0 then WRITE_BITS else 0)
    | (if v & EXEC_BITS != 0 then EXEC_BITS else 0)
  }

  // The bits an action proposes before the who/umask mask. 'X' adds execute bits
  // only if some execute bit is already set (a FIFO is never a directory).
  function RhsBits(r: Rhs, cur: bv32): bv32
    requires r.Octal? ==> OctalValue(r.digits) <= ALLM
  {
    match r
    case Perms(ps) =>
      PermsBits(ps) | (if PermCondX in ps && cur & EXEC_BITS != 0 then EXEC_BITS else 0)
    case Copy(src) => CopyBits(src, cur)
    case Octal(ds) => OctalValue(ds) as bv32
  }

  // An octal right-hand side affects every mode bit, as if "a" were given.
  function ActionScope(who: seq<Who>, a: Action): bv32
  {
    if a.rhs.Octal? then MODE_BITS else WhoBits(who)
  }

  // Without a who list the umask restricts the change; with one, the who bits do.
  function ApplyAction(cur: bv32, umask: bv32, who: seq<Who>, a: Action): bv32
    requires a.rhs.Octal? ==> OctalValue(a.rhs.digits) <= ALLM
  {
    var scope := ActionScope(who, a);
    var v := RhsBits(a.rhs, cur) & (if scope != 0 then scope else !umask);
    match a.op
    case OpSet => (cur & (if scope != 0 then !scope else 0)) | v
    case OpAdd => cur | v
    case OpRemove => cur & !v
  }

  predicate ActionsBounded(as_: seq<Action>)
  {
    forall i :: 0 <= i < |as_| ==>
                  as_[i].rhs.Octal? ==> OctalValue(as_[i].rhs.digits) <= ALLM
  }

  function ApplyActions(cur: bv32, umask: bv32, who: seq<Who>, as_: seq<Action>): bv32
    requires ActionsBounded(as_)
    decreases |as_|
  {
    if |as_| == 0 then cur
    else ApplyActions(ApplyAction(cur, umask, who, as_[0]), umask, who, as_[1..])
  }

  lemma ClauseActionsBounded(c: Clause)
    requires ClauseWellFormed(c)
    ensures ActionsBounded(c.actions)
  {
    forall i | 0 <= i < |c.actions| && c.actions[i].rhs.Octal?
      ensures OctalValue(c.actions[i].rhs.digits) <= ALLM
    {
      assert ActionWellFormed(c.who, c.actions[i], i == |c.actions| - 1);
    }
  }

  function ApplyClauses(cur: bv32, umask: bv32, cs: seq<Clause>): bv32
    requires forall c :: c in cs ==> ClauseWellFormed(c)
    decreases |cs|
  {
    if |cs| == 0 then cur
    else
      ClauseActionsBounded(cs[0]);
      ApplyClauses(ApplyActions(cur, umask, cs[0].who, cs[0].actions), umask, cs[1..])
  }

  // mkfifo starts from a=rw (0666). A numeric mode is used exactly; the umask
  // only matters for symbolic actions without a who list.
  function Meaning(e: ModeExpr, umask: bv32): bv32
    requires WellFormed(e)
  {
    match e
    case Absolute(ds) => OctalValue(ds) as bv32
    case Symbolic(cs) => ApplyClauses(MKFIFO_BASE_MODE, umask, cs)
  }

  // ---------------------------------------------------------------------------
  // What the specification of mkfifo uses
  // ---------------------------------------------------------------------------

  ghost predicate ModeDenotes(s: string, umask: bv32, mode: bv32)
  {
    exists e :: WellFormed(e) && Render(e) == s && mode == Meaning(e, umask)
  }

  ghost predicate ModeInvalid(s: string)
  {
    forall e :: WellFormed(e) ==> Render(e) != s
  }

  // GNU rejects a valid MODE whose result has set-ID or sticky bits:
  // "mode must specify only file permission bits".
  predicate OnlyPermissionBits(mode: bv32)
  {
    mode & !PERMISSION_BITS == 0
  }

  // ===========================================================================
  // Commands
  // ===========================================================================

  // ---------------------------------------------------------------------------
  // Command-line parse errors (GNU getopt_long wording)
  // ---------------------------------------------------------------------------

  // Long options that take no argument, by unique abbreviation.
  function NoArgLongOptionName(token: string): string
  {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var abbreviation := name[2..];
      if CliModel.HasPrefix("help", abbreviation) then "--help"
      else if CliModel.HasPrefix("version", abbreviation) then "--version"
      else name
    else name
  }

  function TryHelpText(): BenchWorld.Bytes
  {
    "Try 'mkfifo --help' for more information.\n"
  }

  function UnknownShortText(byte: BenchWorld.RawByte): BenchWorld.Bytes
  {
    "mkfifo: invalid option -- '" + [byte] + "'\n" + TryHelpText()
  }

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    var t := err.rawToken;
    var isLong := |t| > 2 && t[0] == '-' && t[1] == '-';
    var isShort := |t| > 1 && t[0] == '-' && !isLong;
    if err.kind == CliTypes.UnknownOption then
      if isLong then
        "mkfifo: unrecognized option '" + Utf8.Encode(t) + "'\n" + TryHelpText()
      else if isShort then
        UnknownShortText(Utf8.EncodeChar(t[1])[0])
      else
        "mkfifo: invalid option\n" + TryHelpText()
    else if err.kind == CliTypes.MissingValue then
      if isLong then
        "mkfifo: option '--mode' requires an argument\n" + TryHelpText()
      else
        "mkfifo: option requires an argument -- 'm'\n" + TryHelpText()
    else if err.kind == CliTypes.UnexpectedValue then
      "mkfifo: option '" + Utf8.Encode(NoArgLongOptionName(t)) +
      "' doesn't allow an argument\n" + TryHelpText()
    else
      // The declared long options (mode, help, version) share no prefix, so an
      // ambiguous abbreviation cannot occur.
      "mkfifo: option '" + Utf8.Encode(t) + "' is ambiguous\n" + TryHelpText()
  }

  // ---------------------------------------------------------------------------
  // Fixed text
  // ---------------------------------------------------------------------------

  // TODO: compare byte-for-byte with the pinned GNU binary (_build/coreutils/src/mkfifo --help).
  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: mkfifo [OPTION]... NAME...\n"
    + "Create named pipes (FIFOs) with the given NAMEs.\n"
    + "\n"
    + "Mandatory arguments to long options are mandatory for short options too.\n"
    + "  -m, --mode=MODE\n"
    + "         set file permission bits to MODE, not a=rw - umask\n"
    + "  -Z\n"
    + "         set the SELinux security context to default type\n"
    + "      --context[=CTX]\n"
    + "         like -Z, or if CTX is specified then set the\n"
    + "         SELinux or SMACK security context to CTX\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/mkfifo>\n"
    + "or available locally via: info '(coreutils) mkfifo invocation'\n"
  }

  // TODO: compare with the pinned GNU binary (_build/coreutils/src/mkfifo --version).
  function VersionTextSpec(): BenchWorld.Bytes
  {
    "mkfifo (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie.\n"
  }

  function MissingOperandText(): BenchWorld.Bytes
  {
    "mkfifo: missing operand\nTry 'mkfifo --help' for more information.\n"
  }

  function InvalidModeText(): BenchWorld.Bytes
  {
    "mkfifo: invalid mode\n"
  }

  function SpecialBitsText(): BenchWorld.Bytes
  {
    "mkfifo: mode must specify only file permission bits\n"
  }

  function CreateFailureText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
  {
    "mkfifo: cannot create fifo " + quoted + ": " + Utf8.Encode(reason) + "\n"
  }

  function PermissionFailureText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
  {
    "mkfifo: cannot set permissions of " + quoted + ": " + Utf8.Encode(reason) + "\n"
  }

  // GNU mkfifo quotes both diagnostics with quoteaf.
  ghost function CreateFailure(path: string, err: int): BenchWorld.Bytes
  {
    CreateFailureText(C.QuoteafPathResult(path), C.CLocaleErrnoTextResult(err))
  }

  ghost function PermissionFailure(path: string, err: int): BenchWorld.Bytes
  {
    PermissionFailureText(C.QuoteafPathResult(path), C.CLocaleErrnoTextResult(err))
  }

  // ---------------------------------------------------------------------------
  // MODE decision (made once, before any operand)
  // ---------------------------------------------------------------------------

  datatype ModePlan =
    | NoModeOption                 // no -m: create with 0666, no permission change
    | ExplicitMode(bits: bv32)     // valid MODE within 0777: create, then set bits
    | RejectInvalidMode            // "invalid mode"
    | RejectSpecialBits            // "mode must specify only file permission bits"

  ghost predicate ModePlanOf(raw: Schema.MkfifoCmdRaw, umask: bv32, plan: ModePlan)
  {
    match raw.mode
    case None => plan == NoModeOption
    case Some(s) =>
      (ModeInvalid(s) && plan == RejectInvalidMode) ||
      (exists bits :: ModeDenotes(s, umask, bits) &&
                      plan == (if OnlyPermissionBits(bits) then ExplicitMode(bits) else RejectSpecialBits))
  }

  // ---------------------------------------------------------------------------
  // One operand
  // ---------------------------------------------------------------------------

  datatype OperandOutcome =
    | Created
    | CreateFailed(createErr: int)
    | PermissionFailed(permErr: int)   // the FIFO exists; its permission change failed

  // Without -m: exactly one creation with 0666. With -m: one creation with the
  // MODE bits, then, only if it succeeded, one non-following permission change.
  ghost predicate OperandStep(
    before: BenchWorld.FileSystem, after: BenchWorld.FileSystem, path: string, plan: ModePlan,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    outcome: OperandOutcome)
    requires plan.NoModeOption? || plan.ExplicitMode?
  {
    var createMode := if plan.ExplicitMode? then plan.bits else MKFIFO_BASE_MODE;
    exists created: BenchWorld.FileSystem, ok: bool, err: int ::
      C.CreateSpecialNodeSpec(before, now, fsObservations, umask, created,
                              path, BenchWorld.FifoNode, createMode, 0, 0, ok, err) &&
      if !ok then
        after == created && outcome == CreateFailed(err)
      else if plan.NoModeOption? then
        after == created && outcome == Created
      else
        exists permOk: bool, permErr: int ::
          C.SetFileModeSpec(created, now, failures, after, path, false, plan.bits, permOk, permErr) &&
          outcome == (if permOk then Created else PermissionFailed(permErr))
  }

  ghost function OutcomeDiagnostic(path: string, outcome: OperandOutcome): BenchWorld.Bytes
  {
    match outcome
    case Created => []
    case CreateFailed(err) => CreateFailure(path, err)
    case PermissionFailed(err) => PermissionFailure(path, err)
  }

  // ---------------------------------------------------------------------------
  // All operands
  // ---------------------------------------------------------------------------

  ghost predicate OperandResults(
    paths: seq<string>, plan: ModePlan, states: seq<BenchWorld.FileSystem>, outcomes: seq<OperandOutcome>,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations)
    requires plan.NoModeOption? || plan.ExplicitMode?
  {
    |states| == |paths| + 1 && |outcomes| == |paths| &&
    (forall i | 0 <= i < |paths| ::
       OperandStep(states[i], states[i + 1], paths[i], plan, now, umask,
                   fsObservations, failures, outcomes[i]))
  }

  // Cuts partition stderr in operand order, including empty pieces.
  ghost predicate OrderedDiagnostics(
    paths: seq<string>, outcomes: seq<OperandOutcome>, diagnostics: BenchWorld.Bytes, cuts: seq<nat>)
  {
    |outcomes| == |paths| && |cuts| == |paths| + 1 &&
    cuts[0] == 0 && cuts[|paths|] == |diagnostics| &&
    (forall i {:trigger cuts[i]} | 0 <= i < |paths| ::
       cuts[i] <= cuts[i + 1] <= |diagnostics| &&
       diagnostics[cuts[i]..cuts[i + 1]] == OutcomeDiagnostic(paths[i], outcomes[i]))
  }

  // What a fixed MODE decision does to the filesystem and stderr.
  ghost predicate PlanRun(
    paths: seq<string>, plan: ModePlan,
    before: BenchWorld.FileSystem, after: BenchWorld.FileSystem,
    now: int, umask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    diagnostics: BenchWorld.Bytes, runExit: int)
  {
    match plan
    case RejectInvalidMode =>
      after == before && diagnostics == InvalidModeText() && runExit == 1
    case RejectSpecialBits =>
      after == before && diagnostics == SpecialBitsText() && runExit == 1
    case _ =>
      exists states: seq<BenchWorld.FileSystem>, outcomes: seq<OperandOutcome>, cuts: seq<nat> ::
        OperandResults(paths, plan, states, outcomes, now, umask, fsObservations, failures) &&
        states[0] == before && states[|paths|] == after &&
        OrderedDiagnostics(paths, outcomes, diagnostics, cuts) &&
        runExit == (if forall i | 0 <= i < |paths| :: outcomes[i].Created? then 0 else 1)
  }

  // `createUmask` is the umask the native FIFO creation applies; `modeUmask` is
  // the value GNU reads with umask() to evaluate a symbolic MODE.
  ghost predicate RunRelation(
    raw: Schema.MkfifoCmdRaw,
    before: BenchWorld.FileSystem, after: BenchWorld.FileSystem,
    now: int, createUmask: bv32, modeUmask: bv32,
    fsObservations: C.ValidFilesystemObservations,
    failures: C.ValidNativeFailureObservations,
    diagnostics: BenchWorld.Bytes, runExit: int)
  {
    exists plan: ModePlan ::
      ModePlanOf(raw, modeUmask, plan) &&
      PlanRun(Schema.Operands(raw), plan, before, after, now, createUmask,
              fsObservations, failures, diagnostics, runExit)
  }

  // ---------------------------------------------------------------------------
  // Streams and the main specification
  // ---------------------------------------------------------------------------

  // mkfifo writes nothing to stdout outside help/version. All diagnostics form
  // one stderr write; a failed stderr write also makes the exit status 1.
  ghost predicate StderrResult(
    beforeErr: BenchWorld.Bytes, afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    diagnostics: BenchWorld.Bytes, runExit: int, exit: int)
  {
    var errObservation := observations(BenchWorld.StreamWriteStderr(beforeErr, diagnostics));
    errObservation.StreamWriteResult? &&
    C.WriteStderrSpec(beforeErr, observations, afterErr, diagnostics,
                      errObservation.committed, errObservation.err) &&
    exit == (if runExit == 0 && errObservation.err == 0 then 0 else 1)
  }

  twostate predicate Spec(raw: Schema.MkfifoCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stderrRegion,
          io.nowRegion, io.umaskRegion, io.propsRegion,
          io.trustedFilesystemRegion, io.trustedNativeFailuresRegion, io.trustedStreamsRegion
  {
    exists diagnostics: BenchWorld.Bytes, runExit: int ::
      RunRelation(raw, old(io.fs()), io.fs(), io.now(), io.umask(), C.GetUmaskResultFields(io.props()),
                  io.trustedFilesystem(), io.trustedNativeFailures(), diagnostics, runExit) &&
      StderrResult(old(io.stderr()), io.stderr(), io.trustedStreams(), diagnostics, runExit, exit)
  }
}
