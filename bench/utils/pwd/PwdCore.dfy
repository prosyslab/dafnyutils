include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "PwdSchema.dfy"
include "PwdSpec.dfy"

module PwdCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = PwdSchema
  import BenchWorld
  import Spec = PwdSpec

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetIgnoredOperandsWarning() returns (out: BenchWorld.Bytes)
    ensures out == Spec.IgnoredOperandsWarningSpec()
  {
    out := Spec.IgnoredOperandsWarningSpec();
  }

  method GetCurrentDirectoryText(dir: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.CurrentDirectoryTextSpec(dir)
  {
    out := Spec.CurrentDirectoryTextSpec(dir);
  }

  function ContainsUnsafeComponent(segs: seq<string>, i: nat): bool
    requires i <= |segs|
    decreases |segs| - i
  {
    if i >= |segs| then
      false
    else if segs[i] == "." || segs[i] == ".." then
      true
    else
      ContainsUnsafeComponent(segs, i + 1)
  } by method
  {
    if i >= |segs| {
      return false;
    } else if segs[i] == "." || segs[i] == ".." {
      return true;
    } else {
      return ContainsUnsafeComponent(segs, i + 1);
    }
  }

  function HasValidLogicalPwdForCwd(pwd: string, cwd: string): bool
  {
    BenchWorld.IsAbsolutePath(pwd) &&
    !ContainsUnsafeComponent(BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0), 0) &&
    BenchWorld.NormalizePath(pwd) == cwd
  } by method
  {
    if !BenchWorld.IsAbsolutePath(pwd) {
      return false;
    }

    var segs := BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0);
    var unsafe := ContainsUnsafeComponent(segs, 0);
    if unsafe {
      return false;
    }

    return BenchWorld.NormalizePath(pwd) == cwd;
  }

  function HelpSelected(raw: Schema.PwdCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpOccurrenceIndex > raw.versionOccurrenceIndex)
  }

  function VersionSelected(raw: Schema.PwdCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionOccurrenceIndex > raw.helpOccurrenceIndex)
  }

  ghost function UseLogicalFields(raw: Schema.PwdCmdRaw, env: map<string, string>): bool
  {
    if raw.seenLogical && raw.seenPhysical then
      raw.logicalOccurrenceIndex > raw.physicalOccurrenceIndex
    else if raw.seenLogical then
      true
    else if raw.seenPhysical then
      false
    else
      "POSIXLY_CORRECT" in env
  }

  ghost function SelectedCurrentDirFields(raw: Schema.PwdCmdRaw, cwd: string, env: map<string, string>): string
  {
    if UseLogicalFields(raw, env) then
      if "PWD" in env && HasValidLogicalPwdForCwd(env["PWD"], cwd) then
        env["PWD"]
      else
        cwd
    else
      cwd
  }

  twostate predicate CoreSummary(raw: Schema.PwdCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpSelected(raw) then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionSelected(raw) then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      io.stdout() == old(io.stdout()) + Spec.CurrentDirectoryTextSpec(SelectedCurrentDirFields(raw, old(io.cwd()), old(io.env()))) &&
      io.stderr() == old(io.stderr()) + (if |raw.operands| > 0 then Spec.IgnoredOperandsWarningSpec() else "") &&
      exit == 0
  }

  method RunCore(raw: Schema.PwdCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion
    modifies io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preEnv := io.env();
    ghost var preCwd := io.cwd();
    var helpSelected := HelpSelected(raw);
    if helpSelected {
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    var versionSelected := VersionSelected(raw);
    if versionSelected {
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    var useLogical := false;
    if raw.seenLogical && raw.seenPhysical {
      useLogical := raw.logicalOccurrenceIndex > raw.physicalOccurrenceIndex;
    } else if raw.seenLogical {
      useLogical := true;
    } else if raw.seenPhysical {
      useLogical := false;
    } else {
      var posix := io.GetEnv("POSIXLY_CORRECT");
      assert IOContract.GetEnvContractFields(preEnv, "POSIXLY_CORRECT", posix);
      match posix
      case Ok(_) => useLogical := true;
      case Err(_) => useLogical := false;
    }

    var cwd := io.GetCwd();
    assert cwd == IOContract.GetCwdResultFields(preCwd);
    var dir := cwd;
    if useLogical {
      var pwdResult := io.GetEnv("PWD");
      assert IOContract.GetEnvContractFields(preEnv, "PWD", pwdResult);
      match pwdResult
      case Ok(pwd) =>
        var valid := HasValidLogicalPwdForCwd(pwd, cwd);
        if valid {
          dir := pwd;
        }
      case Err(_) =>
        dir := cwd;
    }

    if |raw.operands| > 0 {
      var warning := GetIgnoredOperandsWarning();
      io.AppendStderr(warning);
    }
    var out := GetCurrentDirectoryText(dir);
    io.AppendStdout(out);
    exit := 0;
    assert dir == SelectedCurrentDirFields(raw, preCwd, preEnv);
    assert CoreSummary(raw, io, exit);
  }
}
