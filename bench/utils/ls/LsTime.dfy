module LsTime {
  datatype CivilDate = CivilDate(year: int, month: nat, day: nat)
  datatype UtcParts = UtcParts(date: CivilDate, hour: nat, minute: nat, second: nat)

  function FloorDiv(value: int, divisor: nat): int
    requires divisor > 0
  {
    if value >= 0 then value / divisor
    else -((-value + divisor - 1) / divisor)
  }

  function FloorMod(value: int, divisor: nat): nat
    requires divisor > 0
  {
    (value - FloorDiv(value, divisor) * divisor) as nat
  }

  // Howard Hinnant's civil-from-days transformation, with day zero at 1970-01-01.
  function CivilFromDays(daysSinceEpoch: int): CivilDate
  {
    var z := daysSinceEpoch + 719468;
    var era := FloorDiv(z, 146097);
    var dayOfEra := z - era * 146097;
    var yearOfEra :=
      (dayOfEra - dayOfEra / 1460 + dayOfEra / 36524 - dayOfEra / 146096) / 365;
    var year := yearOfEra + era * 400;
    var dayOfYear := dayOfEra - (365 * yearOfEra + yearOfEra / 4 - yearOfEra / 100);
    var monthPrime := (5 * dayOfYear + 2) / 153;
    var day := dayOfYear - (153 * monthPrime + 2) / 5 + 1;
    var month := monthPrime + (if monthPrime < 10 then 3 else -9);
    CivilDate(year + (if month <= 2 then 1 else 0), month as nat, day as nat)
  }

  function Digit(d: nat): char
    requires d < 10
  {
    if d == 0 then '0' else if d == 1 then '1' else if d == 2 then '2'
    else if d == 3 then '3' else if d == 4 then '4' else if d == 5 then '5'
    else if d == 6 then '6' else if d == 7 then '7' else if d == 8 then '8' else '9'
  }

  function NatText(value: nat): string
    decreases value
  {
    if value < 10 then [Digit(value)]
    else NatText(value / 10) + [Digit(value % 10)]
  }

  function ZeroesPart1(): string
  {
    "0"
  }

  function Zeroes(count: nat): string
    decreases count
  {
    if count == 0 then [] else ZeroesPart1() + Zeroes(count - 1)
  }

  function PaddedNat(value: nat, width: nat): string
  {
    var text := NatText(value);
    if |text| < width then Zeroes(width - |text|) + text else text
  }

  function YearTextPart1(): string
  {
    "-"
  }

  function YearText(year: int): string
  {
    if 0 <= year < 10000 then PaddedNat(year as nat, 4)
    else if year < 0 then YearTextPart1() + NatText((-year) as nat)
    else NatText(year as nat)
  }

  function MonthNamePart1(): string
  {
    "Jan"
  }

  function MonthNamePart2(): string
  {
    "Feb"
  }

  function MonthNamePart3(): string
  {
    "Mar"
  }

  function MonthNamePart4(): string
  {
    "Apr"
  }

  function MonthNamePart5(): string
  {
    "May"
  }

  function MonthNamePart6(): string
  {
    "Jun"
  }

  function MonthNamePart7(): string
  {
    "Jul"
  }

  function MonthNamePart8(): string
  {
    "Aug"
  }

  function MonthNamePart9(): string
  {
    "Sep"
  }

  function MonthNamePart10(): string
  {
    "Oct"
  }

  function MonthNamePart11(): string
  {
    "Nov"
  }

  function MonthNamePart12(): string
  {
    "Dec"
  }

  function MonthName(month: nat): string
  {
    if month == 1 then MonthNamePart1() else if month == 2 then MonthNamePart2()
    else if month == 3 then MonthNamePart3() else if month == 4 then MonthNamePart4()
    else if month == 5 then MonthNamePart5() else if month == 6 then MonthNamePart6()
    else if month == 7 then MonthNamePart7() else if month == 8 then MonthNamePart8()
    else if month == 9 then MonthNamePart9() else if month == 10 then MonthNamePart10()
    else if month == 11 then MonthNamePart11() else MonthNamePart12()
  }

  function TimeParts(seconds: int): UtcParts
  {
    var dayNumber := FloorDiv(seconds, 86400);
    var secondOfDay := FloorMod(seconds, 86400);
    UtcParts(CivilFromDays(dayNumber), secondOfDay / 3600,
             (secondOfDay % 3600) / 60, secondOfDay % 60)
  }

  function IsRecent(seconds: int, nanoseconds: int, now: int): bool
  {
    var normalized := NormalizeNsec(nanoseconds) as int;
    // Now() observes whole seconds, so every timestamp in the observed second is non-future.
    (now - 15778476 < seconds ||
     (now - 15778476 == seconds && 0 < normalized)) &&
    seconds <= now
  }

  function FullIsoPart1(): string
  {
    "-"
  }

  function FullIsoPart2(): string
  {
    " "
  }

  function FullIsoPart3(): string
  {
    ":"
  }

  function FullIsoPart4(): string
  {
    "."
  }

  function FullIsoPart5(): string
  {
    " +0000"
  }

  function FullIso(seconds: int, nanoseconds: int): string
  {
    var parts := TimeParts(seconds);
    var date := parts.date;
    YearText(date.year) + FullIsoPart1() + PaddedNat(date.month, 2) + FullIsoPart1() +
    PaddedNat(date.day, 2) + FullIsoPart2() + PaddedNat(parts.hour, 2) + FullIsoPart3() +
    PaddedNat(parts.minute, 2) + FullIsoPart3() + PaddedNat(parts.second, 2) + FullIsoPart4() +
    PaddedNat(NormalizeNsec(nanoseconds), 9) + FullIsoPart5()
  }

  function NormalizeNsec(nanoseconds: int): nat
  {
    if 0 <= nanoseconds < 1000000000 then nanoseconds as nat else 0
  }

  function LongIsoPart1(): string
  {
    "-"
  }

  function LongIsoPart2(): string
  {
    " "
  }

  function LongIsoPart3(): string
  {
    ":"
  }

  function LongIso(seconds: int): string
  {
    var parts := TimeParts(seconds);
    var date := parts.date;
    YearText(date.year) + LongIsoPart1() + PaddedNat(date.month, 2) + LongIsoPart1() +
    PaddedNat(date.day, 2) + LongIsoPart2() + PaddedNat(parts.hour, 2) + LongIsoPart3() + PaddedNat(parts.minute, 2)
  }

  function IsoPart1(): string
  {
    "-"
  }

  function IsoPart2(): string
  {
    " "
  }

  function IsoPart3(): string
  {
    ":"
  }

  function Iso(seconds: int, nanoseconds: int, now: int): string
  {
    var parts := TimeParts(seconds);
    var date := parts.date;
    if IsRecent(seconds, nanoseconds, now) then
      PaddedNat(date.month, 2) + IsoPart1() + PaddedNat(date.day, 2) + IsoPart2() +
      PaddedNat(parts.hour, 2) + IsoPart3() + PaddedNat(parts.minute, 2)
    else
      YearText(date.year) + IsoPart1() + PaddedNat(date.month, 2) + IsoPart1() + PaddedNat(date.day, 2) + IsoPart2()
  }

  function DefaultCPart1(): string
  {
    " "
  }

  function DefaultCPart2(): string
  {
    ":"
  }

  function DefaultCPart3(): string
  {
    "  "
  }

  function DefaultC(seconds: int, nanoseconds: int, now: int): string
  {
    var parts := TimeParts(seconds);
    var date := parts.date;
    var dayText := if date.day < 10 then DefaultCPart1() + NatText(date.day) else NatText(date.day);
    if IsRecent(seconds, nanoseconds, now) then
      MonthName(date.month) + DefaultCPart1() + dayText + DefaultCPart1() +
      PaddedNat(parts.hour, 2) + DefaultCPart2() + PaddedNat(parts.minute, 2)
    else
      MonthName(date.month) + DefaultCPart1() + dayText + DefaultCPart3() + YearText(date.year)
  }
}
