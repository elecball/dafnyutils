
module CpPathSpec {
  ghost function IsSlash(ch: char): bool
  {
    ch == '/'
  }

  ghost predicate SlashFree(text: string)
  {
    forall i :: 0 <= i < |text| ==> !IsSlash(text[i])
  }

  ghost predicate SlashesOnly(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsSlash(text[i])
  }

  ghost predicate MaximalSlashFreeSuffix(text: string, suffix: string)
  {
    0 < |suffix| <= |text| &&
    text[|text| - |suffix|..] == suffix &&
    SlashFree(suffix) &&
    (|suffix| == |text| || IsSlash(text[|text| - |suffix| - 1]))
  }

  ghost predicate BasenameRelation(path: string, base: string)
  {
    if |path| == 0 then
      base == ""
    else if SlashesOnly(path) then
      base == "/"
    else
      exists trimmed: string, prefix: string, trailing: string ::
        path == trimmed + trailing &&
        SlashesOnly(trailing) &&
        0 < |trimmed| &&
        !IsSlash(trimmed[|trimmed| - 1]) &&
        trimmed == prefix + base &&
        MaximalSlashFreeSuffix(trimmed, base)
  }

  ghost predicate PathWithoutTrailingSlashes(
    path: string, trimmed: string, trailing: string
  )
  {
    path == trimmed + trailing &&
    SlashesOnly(trailing) &&
    0 < |trimmed| &&
    !IsSlash(trimmed[|trimmed| - 1])
  }

  ghost predicate MaximalDirnamePrefix(
    trimmed: string, prefix: string, component: string
  )
  {
    trimmed == prefix + "/" + component &&
    0 < |component| &&
    SlashFree(component) &&
    (forall i :: 0 <= i < |trimmed| && IsSlash(trimmed[i]) ==> i <= |prefix|)
  }

  ghost predicate NormalizedDirnamePrefix(prefix: string, value: string)
  {
    if |prefix| == 0 then
      value == "/"
    else if SlashesOnly(prefix) then
      value == "/"
    else
      exists trailing: string ::
        prefix == value + trailing &&
        SlashesOnly(trailing) &&
        0 < |value| &&
        !IsSlash(value[|value| - 1])
  }

  opaque ghost predicate DirnameRelation(path: string, value: string)
  {
    if |path| == 0 then
      value == "."
    else if SlashesOnly(path) then
      value == "/"
    else
      exists trimmed: string, trailing: string ::
        PathWithoutTrailingSlashes(path, trimmed, trailing) &&
        (if SlashFree(trimmed) then
           value == "."
         else
           exists prefix: string, component: string ::
             MaximalDirnamePrefix(trimmed, prefix, component) &&
             NormalizedDirnamePrefix(prefix, value))
  }
  ghost function DigitCharSpec(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  ghost function DecimalNatSpec(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitCharSpec(n)]
    else
      DecimalNatSpec(n / 10) + [DigitCharSpec(n % 10)]
  }

  ghost function NumberedBackupPathSpec(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNatSpec(index) + "~"
  }

  ghost function SimpleBackupPathSpec(target: string, suffix: string): string
  {
    target + suffix
  }

}
