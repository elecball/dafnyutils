module DateModel {
  datatype Civil = Civil(year: int, month: int, day: int, hour: int, minute: int, second: int)

  // Number of Gregorian days before March 1 of a proleptic year, up to a constant.
  opaque function MarchYearStart(year: int): int
  {
    365 * year + year / 4 - year / 100 + year / 400
  }

  function Leap(year: int): bool
  {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
  }

  function MarchMonthStart(month: int): int
  {
    (153 * month + 2) / 5
  }

  function MonthLength(year: int, month: int): int
  {
    if month == 2 then (if Leap(year) then 29 else 28)
    else if month in {4, 6, 9, 11} then 30 else 31
  }

  predicate Calendar(seconds: int, civil: Civil)
  {
    1 <= civil.month <= 12 && 1 <= civil.day <= MonthLength(civil.year, civil.month) &&
    0 <= civil.hour < 24 && 0 <= civil.minute < 60 && 0 <= civil.second < 60 &&
    var marchYear := if civil.month <= 2 then civil.year - 1 else civil.year;
    var marchMonth := if civil.month <= 2 then civil.month + 9 else civil.month - 3;
    seconds / 86400 == MarchYearStart(marchYear) + MarchMonthStart(marchMonth) + civil.day - 1 - 719468 &&
    seconds % 86400 == civil.hour * 3600 + civil.minute * 60 + civil.second
  }

  function Power10(n: nat): (p: nat)
    ensures p > 0
    decreases n
  {
    if n == 0 then 1 else 10 * Power10(n - 1)
  }

  ghost predicate Decimal(value: nat, digits: string)
  {
    |digits| > 0 && value < Power10(|digits|) &&
    (|digits| > 1 ==> value >= Power10(|digits| - 1)) &&
    forall i: int | 0 <= i < |digits| ::
      digits[i] as int == '0' as int + (value / Power10(|digits| - 1 - i)) % 10
  }

  ghost predicate NumberText(value: int, width: nat, pad: char, text: string)
  {
    exists digits: string, padding: string ::
      Decimal((if value < 0 then -value else value), digits) &&
      |padding| == (if width > |digits| + (if value < 0 then 1 else 0)
                    then width - |digits| - (if value < 0 then 1 else 0) else 0) &&
      (forall i: int | 0 <= i < |padding| :: padding[i] == pad) &&
      text == (if pad == ' ' then padding + (if value < 0 then "-" else "") + digits
               else (if value < 0 then "-" else "") + padding + digits)
  }
}
