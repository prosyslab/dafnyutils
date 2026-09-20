
module MvPathSpec {
  function IsSlash(ch: char): bool
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
}
