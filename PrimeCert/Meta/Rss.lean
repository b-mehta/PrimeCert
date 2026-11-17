/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-! # A phase log that survives the watchdog

Two definitions, in a module of their own so that both the segment emitter and `run_sieve` can
write to one log. They lived beside the emitter until the base sieve's own phases needed them, and
`PrimeCert.Meta.Sieve` cannot import the emitter.

Nothing here empties the file. Two commands write to it and either may run first, so whichever
truncated it would throw away the other's lines; `run.sh` deletes it before each case instead.
-/

namespace PrimeCert.Sieve

/-- Append a line to `/tmp/skip-rss.log` and flush it.

`logInfo` holds its messages until the command finishes, so a command the watchdog kills prints
none of them, and `IO.getStderr` is no better because the command elaborator runs inside
`IO.FS.withIsolatedStreams` and that handle is the captured stream. A file opened by name is
outside both, which is the whole reason for the path. Read it after the kill; it is not in the
`out-` or `time-` file. -/
public meta def rssLog (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/skip-rss.log" IO.FS.Mode.append
  h.putStrLn s!"skip rss: {msg}"
  h.flush

/-- Resident memory of this process in MiB, from the second field of `/proc/self/statm`, which
counts pages. Returns 0 where that file is not readable, so a platform without it reports zeros
rather than failing a build. -/
public meta def rssMB : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/statm"
    match (s.splitOn " ")[1]? with
    | some p => return ((p.trimAscii.toNat?.getD 0) * 4) / 1024
    | none => return 0
  catch _ => return 0

end PrimeCert.Sieve
