include "../../core/CliTypes.dfy"
include "CliSupport.dfy"

module CpSchema {
  // Keep CLI-only normalization unavailable to candidate runtime code.
  export
    provides CliTypes, CliModel, CliExtern
    provides Schema, ParserConfig, ParseArgs, Decode
    reveals CpMode, CpError, BackupSettings, CreationPolicy, CopyPolicy, CpCmdRaw, ArgumentMatch
    reveals ChildCommand, MatchingArguments, ExactArgument, MatchArgument
    reveals PreserveArguments, UpdateArguments, BackupArguments, BackupMeanings, BackupControl

  import CliTypes
  import CliModel
  import opened CliExtern

  datatype CpMode = Run | Help | Version
  datatype CpError = NoError | TargetConflict | MultipleTargets | LinkConflict |
                     InvalidPreserve(value: string, enable: bool, ambiguous: bool) | InvalidUpdate(value: string, ambiguous: bool) |
                     InvalidBackup(value: string, ambiguous: bool, environment: bool) | BackupConflict
  datatype BackupSettings = BackupSettings(enabled: bool, control: CliTypes.OptionalString, suffix: CliTypes.OptionalString)
  datatype CreationPolicy = CreationPolicy(defaultMode: bool, preserveLinks: bool, parents: bool, backup: BackupSettings, writeDangling: bool)
  datatype CopyPolicy = CopyPolicy(
    recursive: bool, dereference: bool, force: bool, skip: bool, verbose: bool,
    remove: bool, hard: bool, symbolic: bool, attributesOnly: bool,
    preserveMode: bool, preserveTimes: bool, update: string,
    commandLineDereference: bool, oneFileSystem: bool, keepDirectorySymlink: bool, creation: CreationPolicy)
  datatype CpCmdRaw = CpCmdRaw(
    mode: CpMode, operands: seq<string>, target: CliTypes.OptionalString,
    noTarget: bool, policy: CopyPolicy, error: CpError)

  method Schema() returns (schema: CliTypes.CliSchema) {
    schema := CliTypes.CliSchema([
                                   CliTypes.OptionDecl("help", [], ["help"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("version", [], ["version"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("force", ['f'], ["force"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("skip", ['n'], ["no-clobber"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("verbose", ['v'], ["verbose"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("target", ['t'], ["target-directory"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("noTarget", ['T'], ["no-target-directory"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("recursive", ['r', 'R'], ["recursive"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("follow", ['L'], ["dereference"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("commandFollow", ['H'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("oneFileSystem", ['x'], ["one-file-system"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("keepDirectorySymlink", [], ["keep-directory-symlink"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("copyContents", [], ["copy-contents"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("strip", [], ["strip-trailing-slashes"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("noFollow", ['P'], ["no-dereference"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("preserveLinks", ['d'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("hard", ['l'], ["link"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("symbolic", ['s'], ["symbolic-link"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("remove", [], ["remove-destination"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("attributes", [], ["attributes-only"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("preserve", [], ["preserve"], CliTypes.OptArg),
                                   CliTypes.OptionDecl("noPreserve", [], ["no-preserve"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("parents", [], ["parents"], CliTypes.NoArg),
                                   CliTypes.OptionDecl("backup", [], ["backup"], CliTypes.OptArg),
                                   CliTypes.OptionDecl("backupShort", ['b'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("suffix", ['S'], ["suffix"], CliTypes.ReqArg),
                                   CliTypes.OptionDecl("older", ['u'], [], CliTypes.NoArg),
                                   CliTypes.OptionDecl("update", [], ["update"], CliTypes.OptArg)
                                 ], true);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig) {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  function ChildCommand(raw: CpCmdRaw): CpCmdRaw {
    raw.(policy := raw.policy.(dereference := raw.policy.dereference && !raw.policy.commandLineDereference,
                                              commandLineDereference := false))
  }

  // Optional GNU long-option arguments are attached with '='. Keep a bare
  // occurrence bare in ParsedArgs while preventing the shared parser from
  // consuming the following file operand. Required option values are skipped.
  method ParseArgs(argv: seq<string>) returns (result: CliTypes.ParseResult) {
    var schema := Schema();
    var config := ParserConfig();
    var normalized := argv;
    var bare: set<int> := {};
    var i := 1;
    var options := true;
    while i < |argv|
      invariant 0 <= i <= |argv|+1
      invariant |normalized| == |argv|
      decreases |argv|-i
    {
      var token := argv[i];
      if token == "--" { options := false; }
      else if options && |token| > 2 && CliModel.HasPrefix(token,"--") {
        var suffix := token[2..];
        var equal := CliModel.FindChar(suffix,'=');
        var name := if equal >= 0 then suffix[..equal] else suffix;
        var found := CliModel.FindLongOption(schema.options,name,true);
        if found.LongFound? && equal < 0 {
          if found.decl.arity == CliTypes.OptArg {
            normalized := normalized[i := token+"="];
            bare := bare+{i};
          } else if found.decl.arity == CliTypes.ReqArg && i+1 < |argv| { i := i+1; }
        }
      } else if options && |token| > 1 && token[0] == '-' {
        var short := CliModel.ParseShortFrom(argv,schema.options,i,token,1,[]);
        if short.ShortParsed? && short.consumesNext { i := i+1; }
      }
      i := i+1;
    }
    result := Cli.Parse(normalized,schema,config);
    if result.ParseSuccess? {
      var parsed := result.parsed;
      var occurrences := parsed.options;
      i := 0;
      while i < |occurrences|
        invariant 0 <= i <= |occurrences|
        invariant |occurrences| == |parsed.options|
        decreases |occurrences|-i
      {
        var occurrence := occurrences[i];
        if occurrence.tokenIndex in bare && 0 <= occurrence.tokenIndex < |argv| {
          occurrences := occurrences[i := occurrence.(value := CliTypes.None, rawToken := argv[occurrence.tokenIndex])];
        }
        i := i+1;
      }
      result := CliTypes.ParseSuccess(parsed.(options := occurrences));
    }
  }

  datatype ArgumentMatch = Matched(value: string) | Unmatched(ambiguous: bool)

  function MatchingArguments(value: string, names: seq<string>, meanings: seq<string>): seq<string>
    requires |names| == |meanings|
    decreases |names|
  {
    if |names| == 0 then []
    else (if CliModel.HasPrefix(names[0],value) then [meanings[0]] else []) + MatchingArguments(value,names[1..],meanings[1..])
  }

  function ExactArgument(value: string, names: seq<string>, meanings: seq<string>): CliTypes.OptionalString
    requires |names| == |meanings|
    decreases |names|
  {
    if |names| == 0 then CliTypes.None
    else if names[0] == value then CliTypes.Some(meanings[0])
    else ExactArgument(value,names[1..],meanings[1..])
  }

  function MatchArgument(value: string, names: seq<string>, meanings: seq<string>): ArgumentMatch
    requires |names| == |meanings|
  {
    var exact := ExactArgument(value,names,meanings);
    var matches := MatchingArguments(value,names,meanings);
    if exact.Some? then Matched(exact.value)
    else if |matches| > 0 && (forall i | 0 <= i < |matches| :: matches[i] == matches[0]) then Matched(matches[0])
    else Unmatched(|matches| > 0)
  }

  function PreserveArguments(): seq<string> { ["mode","timestamps","ownership","links","context","xattr","all"] }
  function UpdateArguments(): seq<string> { ["all","none","none-fail","older"] }
  function BackupArguments(): seq<string> { ["none","off","simple","never","existing","nil","numbered","t"] }
  function BackupMeanings(): seq<string> { ["off","off","simple","simple","existing","existing","numbered","numbered"] }
  function BackupControl(value: string): ArgumentMatch {
    MatchArgument(value,BackupArguments(),BackupMeanings())
  }

  // CLI normalization is fixed with Decode. Runtime Path helpers are separate
  // candidate-owned declarations and never call this decoder-only routine.
  ghost predicate TrimmedForDecode(path: string, trimmed: string)
  {
    if |path| == 0 then
      trimmed == ""
    else if forall i :: 0 <= i < |path| ==> path[i] == '/' then
      trimmed == "/"
    else
      exists end: int ::
        0 < end <= |path| &&
        trimmed == path[..end] &&
        path[end - 1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/'
  }

  method TrimForDecode(path: string) returns (trimmed: string)
    ensures TrimmedForDecode(path, trimmed)
  {
    if |path| == 0 {
      trimmed := "";
      return;
    }

    var allSlash := true;
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant allSlash ==> forall j :: 0 <= j < i ==> path[j] == '/'
      invariant !allSlash ==> exists j :: 0 <= j < i && path[j] != '/'
      decreases |path| - i
    {
      if path[i] != '/' {
        allSlash := false;
      }
      i := i + 1;
    }

    if allSlash {
      trimmed := "/";
      return;
    }

    var end := |path|;
    while 0 < end && path[end - 1] == '/'
      invariant 0 < end <= |path|
      invariant forall j :: end <= j < |path| ==> path[j] == '/'
      invariant exists j :: 0 <= j < end && path[j] != '/'
      decreases end
    {
      end := end - 1;
    }

    trimmed := path[..end];
  }

  method Decode(parsed: CliTypes.ParsedArgs) returns (raw: CpCmdRaw) {
    var mode := Run;
    var target := CliTypes.None;
    var noTarget, recursive, explicitFollow := false, false, false;
    var follow, force, skip, verbose, remove := true, false, false, false, false;
    var hard, symbolic, attributes, preserveMode, preserveTimes := false, false, false, false, false;
    var commandFollow, oneFileSystem, keepDirectorySymlink, strip := false,false,false,false;
    var update := "all";
    var defaultMode,preserveLinks,parents := false,false,false;
    var backupEnabled := false;
    var backupControl,backupSuffix := CliTypes.None,CliTypes.None;
    var error := NoError;
    var i := 0;
    while i < |parsed.options|
      decreases |parsed.options| - i
    {
      var option := parsed.options[i];
      if option.key == "help" { mode := Help; break; }
      if option.key == "version" { mode := Version; break; }
      if option.key == "target" && option.value.Some? {
        if target.Some? { error := MultipleTargets; }
        target := option.value;
      }
      if option.key == "noTarget" { noTarget := true; }
      if option.key == "recursive" { recursive := true; }
      if option.key == "follow" { follow := true; explicitFollow := true; commandFollow := false; }
      if option.key == "commandFollow" { follow := true; explicitFollow := true; commandFollow := true; }
      if option.key == "oneFileSystem" { oneFileSystem := true; }
      if option.key == "keepDirectorySymlink" { keepDirectorySymlink := true; }
      if option.key == "strip" { strip := true; }
      if option.key == "noFollow" { follow := false; explicitFollow := true; commandFollow := false; }
      if option.key == "force" { force := true; }
      if option.key == "skip" { skip := true; }
      if option.key == "verbose" { verbose := true; }
      if option.key == "remove" { remove := true; }
      if option.key == "preserveLinks" { preserveLinks := true; follow := false; explicitFollow := true; commandFollow := false; }
      if option.key == "hard" { hard := true; }
      if option.key == "symbolic" { symbolic := true; }
      if option.key == "attributes" { attributes := true; }
      if option.key == "parents" { parents := true; }
      if option.key == "backup" || option.key == "backupShort" { backupEnabled := true; }
      if option.key == "backup" && option.value.Some? { backupControl := option.value; }
      if option.key == "suffix" { backupEnabled := true; backupSuffix := option.value; }
      if option.key == "older" { update := "older"; }
      if option.key == "update" {
        var value := if option.value.Some? then option.value.value else "older";
        var matched := MatchArgument(value,UpdateArguments(),UpdateArguments());
        if matched.Unmatched? { error := InvalidUpdate(value,matched.ambiguous); break; }
        update := matched.value;
      }
      if option.key == "preserve" || option.key == "noPreserve" {
        var value := if option.value.Some? then option.value.value else "mode,timestamps,ownership";
        var enable := option.key == "preserve";
        var remaining := value;
        var more := true;
        while more
          decreases |remaining|, if more then 1 else 0
        {
          var comma := CliModel.FindChar(remaining,',');
          var word := if comma < 0 then remaining else remaining[..comma];
          var matched := MatchArgument(word,PreserveArguments(),PreserveArguments());
          if matched.Unmatched? { error := InvalidPreserve(word,enable,matched.ambiguous); break; }
          if matched.value == "mode" || matched.value == "all" { preserveMode := enable; defaultMode := !enable; }
          if matched.value == "timestamps" || matched.value == "all" { preserveTimes := enable; }
          if matched.value == "links" || matched.value == "all" { preserveLinks := enable; }
          // Ownership, xattrs and security contexts have no faithful setters in
          // this IO model. Their preservation remains outside the input domain;
          // disabling them is fully representable and needs no filesystem call.
          if comma < 0 { more := false; }
          else { remaining := remaining[comma+1..]; }
        }
        if error != NoError { break; }
      }
      i := i + 1;
    }
    if error == NoError && noTarget && target.Some? { error := TargetConflict; }
    if error == NoError && hard && symbolic { error := LinkConflict; }
    if skip { update := "none"; }
    if error == NoError && backupEnabled && (skip || update == "none" || update == "none-fail") { error := BackupConflict; }
    if recursive && !explicitFollow && !hard { follow := false; }
    var operands := parsed.positionals;
    if strip {
      var normalized: seq<string> := [];
      var j := 0;
      while j < |operands|
        decreases |operands| - j
      {
        if target.Some? || j+1 < |operands| {
          var value := TrimForDecode(operands[j]);
          normalized := normalized + [value];
        } else { normalized := normalized + [operands[j]]; }
        j := j+1;
      }
      operands := normalized;
    }
    raw := CpCmdRaw(mode, operands, target, noTarget,
                    CopyPolicy(recursive,follow,force,skip,verbose,remove,hard,symbolic,attributes,preserveMode,preserveTimes,update,commandFollow,oneFileSystem,keepDirectorySymlink,CreationPolicy(defaultMode,preserveLinks,parents,BackupSettings(backupEnabled,backupControl,backupSuffix),false)),error);
  }
}
