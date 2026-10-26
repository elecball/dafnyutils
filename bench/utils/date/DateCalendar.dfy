include "DateModel.dfy"

module DateCalendar {
  import M = DateModel

  lemma YearStep(year: int)
    ensures M.MarchYearStart(year + 1) - M.MarchYearStart(year) ==
            (if M.Leap(year + 1) then 366 else 365)
  {
    reveal M.MarchYearStart();
    assert (year + 1) / 4 - year / 4 == (if (year + 1) % 4 == 0 then 1 else 0);
    assert (year + 1) / 100 - year / 100 == (if (year + 1) % 100 == 0 then 1 else 0);
    assert (year + 1) / 400 - year / 400 == (if (year + 1) % 400 == 0 then 1 else 0);
    assert (year + 1) % 400 == 0 ==> (year + 1) % 100 == 0;
    assert (year + 1) % 100 == 0 ==> (year + 1) % 4 == 0;
  }

  lemma EraValue(era: int)
    ensures M.MarchYearStart(400 * era) == 146097 * era
  {
    reveal M.MarchYearStart();
    assert (400 * era) / 4 == 100 * era;
    assert (400 * era) / 100 == 4 * era;
    assert (400 * era) / 400 == era;
  }

  lemma EraStart(era: int)
    ensures M.MarchYearStart(400 * era) == 146097 * era
    ensures M.MarchYearStart(400 * era + 400) == 146097 * (era + 1)
  {
    EraValue(era);
    EraValue(era + 1);
  }

  lemma MonthStep(year: int, month: int)
    requires 0 <= month < 12
    ensures (if month < 11 then M.MarchMonthStart(month + 1)
             else if M.Leap(year + 1) then 366 else 365) - M.MarchMonthStart(month) ==
            M.MonthLength(if month < 10 then year else year + 1,
                          if month < 10 then month + 3 else month - 9)
  {
    if month == 0 {} else if month == 1 {} else if month == 2 {}
    else if month == 3 {} else if month == 4 {} else if month == 5 {}
    else if month == 6 {} else if month == 7 {} else if month == 8 {}
    else if month == 9 {} else if month == 10 {} else {}
  }

  method FindYear(absoluteDay: int) returns (year: int, firstDay: int)
    ensures firstDay == M.MarchYearStart(year)
    ensures firstDay <= absoluteDay < firstDay + (if M.Leap(year + 1) then 366 else 365)
  {
    var era := absoluteDay / 146097;
    EraStart(era);
    year := era * 400;
    firstDay := M.MarchYearStart(year);
    YearStep(year);
    while firstDay + (if M.Leap(year + 1) then 366 else 365) <= absoluteDay
      invariant era * 400 <= year < era * 400 + 400
      invariant firstDay == M.MarchYearStart(year)
      invariant firstDay <= absoluteDay < M.MarchYearStart(era * 400 + 400)
      decreases era * 400 + 400 - year
    {
      YearStep(year);
      if year + 1 == era * 400 + 400 {
        assert false;
      }
      year := year + 1;
      firstDay := M.MarchYearStart(year);
    }
  }

  method FindMonth(year: int, dayOfYear: int) returns (month: int)
    requires 0 <= dayOfYear < (if M.Leap(year + 1) then 366 else 365)
    ensures 0 <= month < 12
    ensures 1 <= dayOfYear - M.MarchMonthStart(month) + 1 <=
            M.MonthLength(if month < 10 then year else year + 1,
                          if month < 10 then month + 3 else month - 9)
  {
    month := 0;
    while month < 11 && M.MarchMonthStart(month + 1) <= dayOfYear
      invariant 0 <= month <= 11
      invariant M.MarchMonthStart(month) <= dayOfYear
      invariant dayOfYear < (if M.Leap(year + 1) then 366 else 365)
      decreases 11 - month
    {
      month := month + 1;
    }
    MonthStep(year, month);
  }

  method {:isolate_assertions} Convert(seconds: int) returns (civil: M.Civil)
    ensures M.Calendar(seconds, civil)
  {
    var absoluteDay := seconds / 86400 + 719468;
    var year, firstDay := FindYear(absoluteDay);
    var dayOfYear := absoluteDay - firstDay;
    var month := FindMonth(year, dayOfYear);
    assert 0 <= seconds % 86400 < 86400;
    civil := M.Civil(if month < 10 then year else year + 1,
                     if month < 10 then month + 3 else month - 9,
                     dayOfYear - M.MarchMonthStart(month) + 1,
                     seconds % 86400 / 3600,
                     seconds % 86400 % 3600 / 60,
                     seconds % 86400 % 3600 % 60);
  }

  lemma ProductLower(left: int, right: int)
    requires 0 <= left && 1 <= right
    ensures left * right >= left
  {
    assert left * (right - 1) >= 0;
    assert left * right == left + left * (right - 1);
  }

  lemma {:isolate_assertions} DivTen(value: nat, divisor: nat)
    requires divisor > 0
    ensures value / (10 * divisor) == (value / 10) / divisor
  {
    var q := (value / 10) / divisor;
    var r := (value / 10) % divisor;
    assert value == 10 * (divisor * q + r) + value % 10;
    assert value == (10 * divisor) * q + (10 * r + value % 10);
    assert 0 <= 10 * r + value % 10 < 10 * divisor;
    var actual := value / (10 * divisor);
    assert value == (10 * divisor) * actual + value % (10 * divisor);
    assert (10 * divisor) * (actual - q) == 10 * r + value % 10 - value % (10 * divisor);
    if actual > q { ProductLower(10 * divisor, actual - q); }
    if actual < q { ProductLower(10 * divisor, q - actual); }
  }

  method {:isolate_assertions} Digits(value: nat) returns (digits: string)
    ensures M.Decimal(value, digits)
    decreases value
  {
    if value < 10 {
      digits := [('0' as int + value) as char];
    } else {
      var prefix := Digits(value / 10);
      digits := prefix + [('0' as int + value % 10) as char];
      assert value < M.Power10(|digits|);
      assert value >= M.Power10(|digits| - 1);
      forall i: int | 0 <= i < |digits|
        ensures digits[i] as int == '0' as int + (value / M.Power10(|digits| - 1 - i)) % 10
      {
        if i < |prefix| {
          DivTen(value, M.Power10(|prefix| - 1 - i));
        }
      }
    }
  }

  method Number(value: int, width: nat, pad: char := '0') returns (text: string)
    ensures M.NumberText(value, width, pad, text)
  {
    var digits := Digits(if value < 0 then -value else value);
    var count := if width > |digits| + (if value < 0 then 1 else 0)
    then width - |digits| - (if value < 0 then 1 else 0) else 0;
    var padding := "";
    while |padding| < count
      invariant |padding| <= count
      invariant forall i: int | 0 <= i < |padding| :: padding[i] == pad
      decreases count - |padding|
    {
      padding := padding + [pad];
    }
    text := if pad == ' ' then padding + (if value < 0 then "-" else "") + digits
    else (if value < 0 then "-" else "") + padding + digits;
  }
}
