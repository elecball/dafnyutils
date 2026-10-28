include "DateSchema.dfy"
include "DateModel.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/StringEscaping.dfy"

module DateSpec {
  import IO = BenchIO
  import W = BenchWorld
  import C = IOContract
  import Cli = CliTypes
  import U = Utf8Semantics
  import S = DateSchema
  import M = DateModel
  import SE = StringEscaping

  datatype Atom = Numeric(value: int, width: nat, pad: char) | Text(text: string)
  datatype Selection = Instant(seconds: int, nanoseconds: int) | SelectionError(diagnostic: W.Bytes)
  datatype ErrorKind = FileFailure | InvalidDate | ExtraOperand | LeadingPlus | Exclusive | MultipleFormats | Range | WriteFailure

  function ErrorText(kind: ErrorKind, quoted: W.Bytes := [], reason: string := ""): W.Bytes
  {
    if kind == FileFailure then "date: " + quoted + ": " + U.Encode(reason) + "\n"
    else if kind == InvalidDate then "date: invalid date " + quoted + "\n"
    else if kind == ExtraOperand then "date: extra operand " + quoted + "\n" + TryHelp()
    else if kind == LeadingPlus then "date: the argument " + quoted + " lacks a leading '+';\n" +
                                     "when using an option to specify date(s), any non-option\n" +
                                     "argument must be a format string beginning with '+'\n" + TryHelp()
    else if kind == Exclusive then "date: the options to specify dates for printing are mutually exclusive\n" + TryHelp()
    else if kind == MultipleFormats then "date: multiple output formats specified\n"
    else if kind == Range then "date: time " + quoted + " is out of range\n"
    else "date: write error: " + U.Encode(reason) + "\n"
  }

  function TryHelp(): W.Bytes { "Try 'date --help' for more information.\n" }

  function HelpText(): W.Bytes
  {
    "Usage: date [OPTION]... [+FORMAT]\n" +
    "  or:  date [OPTION]... MMDDhhmm[[CC]YY][.ss]\n" +
    "Display date and time in the given FORMAT.\n" +
    "With -s, or with MMDDhhmm[[CC]YY][.ss], set the date and time first.\n" +
    "\n" +
    "Mandatory arguments to long options are mandatory for short options too.\n" +
    "  -d, --date=STRING\n" +
    "         display time described by STRING, not 'now'\n" +
    "      --debug\n" +
    "         annotate the parsed date,\n" +
    "         and warn about questionable usage to standard error\n" +
    "  -f, --file=DATEFILE\n" +
    "         like --date; once for each line of DATEFILE;\n" +
    "         if DATEFILE is -, read names from standard input\n" +
    "  -I[FMT], --iso-8601[=FMT]\n" +
    "         output date/time in ISO 8601 format.\n" +
    "         FMT='date' (default), 'hours', 'minutes', 'seconds', or 'ns'\n" +
    "         for date and time to the indicated precision.\n" +
    "         Example: 2006-08-14T02:34:56-06:00\n" +
    "      --resolution\n" +
    "         output the available resolution of timestamps.\n" +
    "         Example: 0.000000001\n" +
    "  -R, --rfc-email\n" +
    "         output date and time in RFC 5322 format.\n" +
    "         Example: Mon, 14 Aug 2006 02:34:56 +0000\n" +
    "      --rfc-3339=FMT\n" +
    "         output date/time in RFC 3339 format.\n" +
    "         FMT='date', 'seconds', or 'ns'\n" +
    "         for date and time to the indicated precision.\n" +
    "         Example: 2006-08-14 02:34:56-06:00\n" +
    "  -r, --reference=FILE\n" +
    "         display the last modification time of FILE\n" +
    "  -s, --set=STRING\n" +
    "         set time described by STRING\n" +
    "  -u, --utc, --universal\n" +
    "         print or set Coordinated Universal Time (UTC)\n" +
    "      --help\n" +
    "         display this help and exit\n" +
    "      --version\n" +
    "         output version information and exit\n" +
    "\n" +
    "All options that specify the date to display are mutually exclusive.\n" +
    "I.e.: --date, --file, --reference, --resolution.\n" +
    "\n" +
    "FORMAT controls the output.  Interpreted sequences are:\n" +
    "\n" +
    "  %%   a literal %\n" +
    "  %a   locale's abbreviated weekday name (e.g., Sun)\n" +
    "  %A   locale's full weekday name (e.g., Sunday)\n" +
    "  %b   locale's abbreviated month name (e.g., Jan)\n" +
    "  %B   locale's full month name (e.g., January)\n" +
    "  %c   locale's date and time (e.g., Thu Mar  3 23:05:25 2005)\n" +
    "  %C   century; like %Y, except omit last two digits (e.g., 20)\n" +
    "  %d   day of month (e.g., 01)\n" +
    "  %D   date (ambiguous); same as %m/%d/%y\n" +
    "  %e   day of month, space padded; same as %_d\n" +
    "  %F   full date; like %+4Y-%m-%d\n" +
    "  %g   last two digits of year of ISO week number (ambiguous; 00-99); see %G\n" +
    "  %G   year of ISO week number; normally useful only with %V\n" +
    "  %h   same as %b\n" +
    "  %H   hour (00..23)\n" +
    "  %I   hour (01..12)\n" +
    "  %j   day of year (001..366)\n" +
    "  %k   hour, space padded ( 0..23); same as %_H\n" +
    "  %l   hour, space padded ( 1..12); same as %_I\n" +
    "  %m   month (01..12)\n" +
    "  %M   minute (00..59)\n" +
    "  %n   a newline\n" +
    "  %N   nanoseconds (000000000..999999999)\n" +
    "  %p   locale's equivalent of either AM or PM; blank if not known\n" +
    "  %P   like %p, but lower case\n" +
    "  %q   quarter of year (1..4)\n" +
    "  %r   locale's 12-hour clock time (e.g., 11:11:04 PM)\n" +
    "  %R   24-hour hour and minute; same as %H:%M\n" +
    "  %s   seconds since the Epoch (1970-01-01 00:00 UTC)\n" +
    "  %S   second (00..60)\n" +
    "  %t   a tab\n" +
    "  %T   time; same as %H:%M:%S\n" +
    "  %u   day of week (1..7); 1 is Monday\n" +
    "  %U   week number of year, with Sunday as first day of week (00..53)\n" +
    "  %V   ISO week number, with Monday as first day of week (01..53)\n" +
    "  %w   day of week (0..6); 0 is Sunday\n" +
    "  %W   week number of year, with Monday as first day of week (00..53)\n" +
    "  %x   locale's date (can be ambiguous; e.g., 12/31/99)\n" +
    "  %X   locale's time representation (e.g., 23:13:48)\n" +
    "  %y   last two digits of year (ambiguous; 00..99)\n" +
    "  %Y   year\n" +
    "  %z   +hhmm numeric time zone (e.g., -0400)\n" +
    "  %:z  +hh:mm numeric time zone (e.g., -04:00)\n" +
    "  %::z  +hh:mm:ss numeric time zone (e.g., -04:00:00)\n" +
    "  %:::z  numeric time zone with : to necessary precision (e.g., -04, +05:30)\n" +
    "  %Z   alphabetic time zone abbreviation (e.g., EDT)\n" +
    "\n" +
    "By default, date pads numeric fields with zeroes.\n" +
    "The following optional flags may follow '%':\n" +
    "\n" +
    "  -  (hyphen) do not pad the field\n" +
    "  _  (underscore) pad with spaces\n" +
    "  0  (zero) pad with zeros\n" +
    "  +  pad with zeros, and put '+' before future years with >4 digits\n" +
    "  ^  use upper case if possible\n" +
    "  #  use opposite case if possible\n" +
    "\n" +
    "After any flags comes an optional field width, as a decimal number;\n" +
    "then an optional modifier, which is either\n" +
    "E to use the locale's alternate representations if available, or\n" +
    "O to use the locale's alternate numeric symbols if available.\n" +
    "\n" +
    "Examples:\n" +
    "Convert seconds since the Epoch (1970-01-01 UTC) to a date\n" +
    "  $ date --date='@2147483647'\n" +
    "\n" +
    "Show the time on the west coast of the US (use tzselect(1) to find TZ)\n" +
    "  $ TZ='America/Los_Angeles' date\n" +
    "\n" +
    "Show the local time for 9AM next Friday on the west coast of the US\n" +
    "  $ date --date='TZ=\"America/Los_Angeles\" 09:00 next Fri'\n" +
    "\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/date>\n" +
    "or available locally via: info '(coreutils) date invocation'\n"
  }

  function VersionText(): W.Bytes
  {
    "date (GNU coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n" +
    "\n" +
    "Written by David MacKenzie.\n"
  }

  function LongOptions(): seq<string>
  { ["date", "debug", "file", "iso-8601", "reference", "resolution", "rfc-email", "rfc-822", "rfc-2822", "rfc-3339", "set", "uct", "utc", "universal", "help", "version"] }

  function ParseMessage(kind: Cli.ParseErrorKind, raw: string, short: char, name: string, possibilities: string): W.Bytes
  {
    U.Encode(if kind == Cli.Ambiguous then "date: option '" + raw + "' is ambiguous; possibilities:" + possibilities + "\n"
             else if kind == Cli.MissingValue then
               (if |raw| > 2 && raw[..2] == "--" then "date: option '" + raw + "' requires an argument\n"
                else "date: option requires an argument -- '" + [short] + "'\n")
             else if kind == Cli.UnexpectedValue then "date: option '" + name + "' doesn't allow an argument\n"
             else if |raw| > 2 && raw[..2] == "--" then "date: unrecognized option '" + raw + "'\n"
             else "date: invalid option -- '" + [short] + "'\n") + TryHelp()
  }

  function Possibility(name: string): string { " '--" + name + "'" }

  function Shortcut(format: S.Format): string
  {
    match format
    case Default => "%a %b %e %H:%M:%S %Z %Y"
    case IsoDate => "%Y-%m-%d"
    case IsoHours => "%Y-%m-%dT%H%:z"
    case IsoMinutes => "%Y-%m-%dT%H:%M%:z"
    case IsoSeconds => "%Y-%m-%dT%H:%M:%S%:z"
    case IsoNs => "%Y-%m-%dT%H:%M:%S,%N%:z"
    case RfcEmail => "%a, %d %b %Y %H:%M:%S %z"
    case RfcDate => "%Y-%m-%d"
    case RfcSeconds => "%Y-%m-%d %H:%M:%S%:z"
    case RfcNs => "%Y-%m-%d %H:%M:%S.%N%:z"
  }

  function OutputFormat(raw: S.DateCmdRaw): string
  {
    if |raw.operands| == 1 && |raw.operands[0]| > 0 && raw.operands[0][0] == '+'
    then raw.operands[0][1..] else Shortcut(raw.format)
  }

  function Early(raw: S.DateCmdRaw): bool
  {
    raw.mode != S.Run || (raw.date.Some? && raw.reference.Some?) ||
    |raw.operands| > 1 ||
    (|raw.operands| == 1 &&
     ((|raw.operands[0]| == 0 || raw.operands[0][0] != '+') || raw.optionFormat))
  }

  ghost predicate EarlyPlan(raw: S.DateCmdRaw, stdout: W.Bytes, stderr: W.Bytes, code: int)
  {
    if raw.mode == S.Help then stdout == HelpText() && stderr == [] && code == 0
    else if raw.mode == S.Version then stdout == VersionText() && stderr == [] && code == 0
    else
      stdout == [] && code == 1 &&
      (if raw.mode == S.InvalidIso || raw.mode == S.InvalidRfc then
         stderr == InvalidFormatText(raw.mode == S.InvalidIso,
                                     C.QuoteArgumentResult(U.Encode(raw.invalidValue)), raw.invalidValue == "")
       else if raw.date.Some? && raw.reference.Some? then stderr == ErrorText(Exclusive)
       else if |raw.operands| > 1 then
         stderr == ErrorText(ExtraOperand, C.QuoteArgumentResult(U.Encode(raw.operands[1])))
       else if |raw.operands| == 1 && (|raw.operands[0]| == 0 || raw.operands[0][0] != '+') then
         stderr == ErrorText(if raw.date.Some? || raw.reference.Some? then LeadingPlus else InvalidDate,
                             C.QuoteArgumentResult(U.Encode(raw.operands[0])))
       else stderr == ErrorText(MultipleFormats))
  }

  function InvalidFormatText(iso: bool, quoted: W.Bytes, ambiguous: bool := false): W.Bytes
  {
    (if ambiguous then "date: ambiguous argument " else "date: invalid argument ") + quoted + (if iso then " for '--iso-8601'\n" else " for '--rfc-3339'\n") +
    "Valid arguments are:\n" +
    (if iso then "  - 'hours'\n  - 'minutes'\n" else "") +
    "  - 'date'\n  - 'seconds'\n  - 'ns'\n" + TryHelp()
  }

  function Times(result: W.IOResult<W.FileTimeStatus>): W.FileTimeStatus
  {
    C.ResultValue(result, W.FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0))
  }

  ghost predicate Selected(raw: S.DateCmdRaw, fs: W.FileSystem, now: int,
                           parses: map<W.TimeParseRequest, W.ParsedTimeResult>,
                           filesystem: W.TrustedFilesystemRequest -> W.TrustedFilesystemResult,
                           selection: Selection)
  {
    if raw.reference.Some? then
      exists result: W.IOResult<W.FileTimeStatus> ::
        C.GetFileTimesSpec(fs, filesystem, raw.reference.value, true, result.Ok?,
                           Times(result).atimeSec, Times(result).atimeNsec, Times(result).mtimeSec, Times(result).mtimeNsec,
                           Times(result).isDir, Times(result).isSymlink, Times(result).device, Times(result).inode,
                           Times(result).linkCount, C.ResultErrno(result)) &&
        selection == (if result.Ok? then Instant(Times(result).mtimeSec, Times(result).mtimeNsec)
                      else SelectionError(ErrorText(FileFailure, SE.SpecQuoteFBytes(U.Encode(raw.reference.value)),
                                                    C.CLocaleErrnoTextResult(C.ResultErrno(result)))))
    else if raw.date.Some? then
      var result := C.TrustedTimeParseResultFields(parses, W.DateParseRequest(raw.date.value, now, 0));
      selection == (if result.ok then Instant(result.sec, result.nsec)
                    else SelectionError(ErrorText(InvalidDate, C.QuoteArgumentResult(U.Encode(raw.date.value)))))
    else selection == Instant(now, 0)
  }

  function Weekday(seconds: int): int { (seconds / 86400 + 4) % 7 }
  function Ordinal(seconds: int, year: int): int
  { seconds / 86400 + 719468 - M.MarchYearStart(year - 1) - 305 }
  function IsoThursday(seconds: int): int
  { seconds + (3 - (seconds / 86400 + 3) % 7) * 86400 }

  function Meaning(code: char, seconds: int, nanos: int, civil: M.Civil, iso: M.Civil): seq<Atom>
  {
    var y := Numeric(civil.year, 4, '0');
    var m := Numeric(civil.month, 2, '0');
    var d := Numeric(civil.day, 2, '0');
    var h := Numeric(civil.hour, 2, '0');
    var minute := Numeric(civil.minute, 2, '0');
    var second := Numeric(civil.second, 2, '0');
    var month := Text(MonthName(civil.month, false));
    var weekday := Text(WeekdayName(Weekday(seconds), false));
    var hour12 := Numeric((civil.hour + 11) % 12 + 1, 2, '0');
    var ampm := Text(if civil.hour < 12 then "AM" else "PM");
    var colon := Text(":");
    var slash := Text("/");
    var dash := Text("-");
    var space := Text(" ");
    if code == '%' then [Text("%")]
    else if code == 'Y' then [y]
    else if code == 'm' then [m]
    else if code == 'd' then [d]
    else if code == 'H' then [h]
    else if code == 'M' then [minute]
    else if code == 'S' then [second]
    else if code == 's' then [Numeric(seconds, 1, '0')]
    else if code == 'N' then [Numeric(nanos, 9, '0')]
    else if code == 'a' then [weekday]
    else if code == 'A' then [Text(WeekdayName(Weekday(seconds), true))]
    else if code == 'b' || code == 'h' then [month]
    else if code == 'B' then [Text(MonthName(civil.month, true))]
    else if code == 'C' then (if civil.year < 0 then [Text("-"), Numeric((-civil.year) / 100, 1, '0')] else [Numeric(civil.year / 100, 2, '0')])
    else if code == 'y' then [Numeric((if civil.year < 0 then -civil.year else civil.year) % 100, 2, '0')]
    else if code == 'e' then [Numeric(civil.day, 2, ' ')]
    else if code == 'k' then [Numeric(civil.hour, 2, ' ')]
    else if code == 'l' then [Numeric((civil.hour + 11) % 12 + 1, 2, ' ')]
    else if code == 'I' then [hour12]
    else if code == 'j' then [Numeric(Ordinal(seconds, civil.year), 3, '0')]
    else if code == 'u' then [Numeric((seconds / 86400 + 3) % 7 + 1, 1, '0')]
    else if code == 'w' then [Numeric(Weekday(seconds), 1, '0')]
    else if code == 'q' then [Numeric((civil.month - 1) / 3 + 1, 1, '0')]
    else if code == 'U' then [Numeric((Ordinal(seconds, civil.year) + 6 - Weekday(seconds)) / 7, 2, '0')]
    else if code == 'W' then [Numeric((Ordinal(seconds, civil.year) + 6 - (seconds / 86400 + 3) % 7) / 7, 2, '0')]
    else if code == 'G' then [Numeric(iso.year, 4, '0')]
    else if code == 'g' then [Numeric((if iso.year < 0 then -iso.year else iso.year) % 100, 2, '0')]
    else if code == 'V' then [Numeric((Ordinal(IsoThursday(seconds), iso.year) - 1) / 7 + 1, 2, '0')]
    else if code == 'p' then [ampm]
    else if code == 'P' then [Text(if civil.hour < 12 then "am" else "pm")]
    else if code == 'n' then [Text("\n")]
    else if code == 't' then [Text("\t")]
    else if code == 'z' then [Text("+0000")]
    else if code == 'Z' then [Text("UTC")]
    else if code == 'T' || code == 'X' then [h, colon, minute, colon, second]
    else if code == 'R' then [h, colon, minute]
    else if code == 'r' then [hour12, colon, minute, colon, second, space, ampm]
    else if code == 'D' then [m, slash, d, slash, Numeric((if civil.year < 0 then -civil.year else civil.year) % 100, 2, '0')]
    else if code == 'x' then [m, slash, d, slash, Numeric(civil.year % 100, 2, '0')]
    else if code == 'F' then [Text(if civil.year >= 10000 then "+" else ""), y, dash, m, dash, d]
    else if code == 'c' then [weekday, space, month, space, Numeric(civil.day, 2, ' '), space,
                              h, colon, minute, colon, second, space, Numeric(civil.year, 1, '0')]
    else [Text("%" + [code])]
  }

  function MonthName(month: int, full: bool): string
  {
    var abbreviated := map[1 := "Jan", 2 := "Feb", 3 := "Mar", 4 := "Apr", 5 := "May", 6 := "Jun",
                           7 := "Jul", 8 := "Aug", 9 := "Sep", 10 := "Oct", 11 := "Nov", 12 := "Dec"];
    var names := map[1 := "January", 2 := "February", 3 := "March", 4 := "April", 5 := "May", 6 := "June",
                     7 := "July", 8 := "August", 9 := "September", 10 := "October", 11 := "November", 12 := "December"];
    if month in names then (if full then names[month] else abbreviated[month]) else ""
  }

  function WeekdayName(weekday: int, full: bool): string
  {
    var short := map[0 := "Sun", 1 := "Mon", 2 := "Tue", 3 := "Wed", 4 := "Thu", 5 := "Fri", 6 := "Sat"];
    var names := map[0 := "Sunday", 1 := "Monday", 2 := "Tuesday", 3 := "Wednesday", 4 := "Thursday", 5 := "Friday", 6 := "Saturday"];
    if weekday in names then (if full then names[weekday] else short[weekday]) else ""
  }

  ghost predicate AtomText(atom: Atom, text: string)
  {
    match atom
    case Numeric(value, width, pad) => M.NumberText(value, width, pad, text)
    case Text(value) => text == value
  }

  ghost predicate AtomPartition(atoms: seq<Atom>, text: string, cuts: seq<nat>)
  {
    |cuts| == |atoms| + 1 && cuts[0] == 0 && cuts[|atoms|] == |text| &&
    (forall i: int | 0 <= i < |cuts| :: cuts[i] <= |text|) &&
    (forall i: int | 0 <= i < |atoms| :: cuts[i] <= cuts[i + 1] && AtomText(atoms[i], text[cuts[i]..cuts[i + 1]]))
  }

  ghost predicate Token(format: string, lo: nat, hi: nat, seconds: int, nanos: int,
                        civil: M.Civil, iso: M.Civil, text: string)
  {
    lo < hi <= |format| &&
    if format[lo] != '%' then hi == lo + 1 && text == [format[lo]]
    else if lo + 1 == |format| then hi == lo + 1 && text == "%"
    else if lo + 2 < |format| && format[lo + 1] == ':' && format[lo + 2] == 'z' then
      hi == lo + 3 && text == "+00:00"
    else if lo + 3 < |format| && format[lo + 1..lo + 3] == "::" && format[lo + 3] == 'z' then
      hi == lo + 4 && text == "+00:00:00"
    else if lo + 4 < |format| && format[lo + 1..lo + 4] == ":::" && format[lo + 4] == 'z' then
      hi == lo + 5 && text == "+00"
    else hi == lo + 2 && exists cuts: seq<nat> {:trigger AtomPartition(Meaning(format[lo + 1], seconds, nanos, civil, iso), text, cuts)} :: AtomPartition(Meaning(format[lo + 1], seconds, nanos, civil, iso), text, cuts)
  }

  ghost predicate FormatPartition(format: string, seconds: int, nanos: int,
                                  civil: M.Civil, iso: M.Civil, text: string, inputCuts: seq<nat>, outputCuts: seq<nat>)
  {
    |inputCuts| == |outputCuts| && |inputCuts| > 0 && inputCuts[0] == 0 && outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |format| && outputCuts[|outputCuts| - 1] == |text| &&
    (forall i: int | 0 <= i < |inputCuts| :: inputCuts[i] <= |format| && outputCuts[i] <= |text|) &&
    (forall i: int | 0 <= i < |inputCuts| - 1 ::
       inputCuts[i] < inputCuts[i + 1] && outputCuts[i] <= outputCuts[i + 1] &&
       Token(format, inputCuts[i], inputCuts[i + 1], seconds, nanos, civil, iso,
             text[outputCuts[i]..outputCuts[i + 1]]))
  }

  ghost predicate Formatted(format: string, seconds: int, nanos: int, civil: M.Civil, iso: M.Civil, text: string)
  { exists inputCuts: seq<nat>, outputCuts: seq<nat> :: FormatPartition(format, seconds, nanos, civil, iso, text, inputCuts, outputCuts) }

  ghost predicate TimeOutput(format: string, seconds: int, nanos: int, stdout: W.Bytes, stderr: W.Bytes, code: int)
  {
    exists civil: M.Civil, iso: M.Civil ::
      M.Calendar(seconds, civil) && M.Calendar(IsoThursday(seconds), iso) &&
      if -2147481748 <= civil.year <= 2147485547 then
        stderr == [] && code == 0 && exists text: string :: Formatted(format, seconds, nanos, civil, iso, text) && stdout == U.Encode(text + "\n")
      else stdout == "\n" && code == 1 && exists text: string ::
             M.NumberText(seconds, 1, '0', text) && stderr == ErrorText(Range, C.QuoteArgumentResult(U.Encode(text)))
  }

  ghost predicate Plan(raw: S.DateCmdRaw, fs: W.FileSystem, now: int,
                       parses: map<W.TimeParseRequest, W.ParsedTimeResult>, filesystem: W.TrustedFilesystemRequest -> W.TrustedFilesystemResult,
                       stdout: W.Bytes, stderr: W.Bytes, code: int)
  {
    if Early(raw) then EarlyPlan(raw, stdout, stderr, code)
    else
      (exists selection: Selection ::
         Selected(raw, fs, now, parses, filesystem, selection) &&
         (match selection
          case SelectionError(diagnostic) => stdout == [] && stderr == diagnostic && code == 1
          case Instant(seconds, nanos) => TimeOutput(OutputFormat(raw), seconds, nanos, stdout, stderr, code)))
  }

  ghost predicate Emitted(beforeOut: W.Bytes, beforeErr: W.Bytes, afterOut: W.Bytes, afterErr: W.Bytes,
                          streams: W.TrustedStreamRequest -> W.TrustedStreamResult, stdout: W.Bytes, stderr: W.Bytes, code: int, exit: int)
  {
    var out := streams(W.StreamWriteStdout(beforeOut, stdout));
    out.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut, streams, afterOut, stdout, out.committed, out.err) &&
    var diagnostic := stderr + (if out.err == 0 then [] else ErrorText(WriteFailure, [], C.CLocaleErrnoTextResult(out.err)));
    var error := streams(W.StreamWriteStderr(beforeErr, diagnostic));
    error.StreamWriteResult? &&
    C.WriteStderrSpec(beforeErr, streams, afterErr, diagnostic, error.committed, error.err) &&
    exit == (if out.err == 0 && error.err == 0 then code else 1)
  }

  twostate predicate Spec(raw: S.DateCmdRaw, io: IO.IO, exit: int)
    reads io.fsRegion, io.nowRegion, io.trustedTimeParsesRegion, io.trustedFilesystemRegion,
          io.trustedStreamsRegion, io.stdoutRegion, io.stderrRegion
  {
    exists stdout: W.Bytes, stderr: W.Bytes, code: int ::
      Plan(raw, io.fs(), io.now(), io.trustedTimeParses(), io.trustedFilesystem(), stdout, stderr, code) &&
      Emitted(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(), io.trustedStreams(), stdout, stderr, code, exit)
  }
}
