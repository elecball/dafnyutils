include "World.dfy"

module CliTypes {
  import BW = BenchWorld
  datatype OptionArity = NoArg | ReqArg | OptArg
  datatype ArgOrderPolicy = GNU_Permute | POSIX_StopAtFirst

  datatype OptionDecl = OptionDecl(
    key: string,
    shorts: seq<char>,
    longs: seq<string>,
    arity: OptionArity
  )

  datatype CliSchema = CliSchema(
    options: seq<OptionDecl>,
    supportsDoubleDash: bool
  )

  datatype ParseConfig = ParseConfig(
    order: ArgOrderPolicy,
    allowBundling: bool,
    allowLongAbbrev: bool,
    treatDashAsOperand: bool
  )

  datatype OptionSource = Short(ch: char) | Long(name: string)
  datatype OptionalString = None | Some(value: string)

  datatype OptOccurrence = OptOccurrence(
    key: string,
    src: OptionSource,
    value: OptionalString,
    tokenIndex: int,
    rawToken: string
  )

  datatype ParsedArgs = ParsedArgs(
    prog: string,
    options: seq<OptOccurrence>,
    positionals: seq<string>,
    sawDoubleDash: bool
  )

  datatype ParseErrorKind = UnknownOption | MissingValue | UnexpectedValue | Ambiguous
  datatype ParseError = ParseError(kind: ParseErrorKind, tokenIndex: int, rawToken: string)
  datatype ParseResult = ParseSuccess(parsed: ParsedArgs) | ParseFailure(error: ParseError)
  datatype PriorRequest = RequestNone | RequestHelp | RequestVersion
  datatype CliPlan<CmdRaw> =
    | CliRun(raw: CmdRaw)
    | CliEarlyExit(exit: int, stdout: BW.RawBytes, stderr: BW.RawBytes)
}
