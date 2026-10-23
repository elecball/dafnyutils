include "../../bench/core/IO.dfy"

module StreamContractAdmissibilityRegression {
  import opened BenchWorld
  import C = IOContract
  import E = Errnos
  import IO = BenchIO

  ghost function WithObservation(request: TrustedStreamRequest, observed: TrustedStreamResult): C.ValidStreamObservations
    requires C.ValidStreamObservation(request, observed)
  {
    (current: TrustedStreamRequest) =>
      if current == request then observed else C.StreamFailureWitness(current)
  }

  // The public stream observer exposes a validated provider without caller hypotheses.
  lemma StreamObserverExposesValidity(io: IO.IO)
    ensures C.StreamObservationsValid(io.trustedStreams())
  {
  }

  // The public time observer exposes a validated map without caller hypotheses.
  lemma TimeObserverExposesValidity(io: IO.IO)
    ensures C.TimeParseObservationsValid(io.trustedTimeParses())
  {
  }

  // A write-shaped observation cannot satisfy a file-read outcome.
  lemma WrongFileReadConstructor(fs: FileSystem, path: Path, data: Bytes, err: int, stage: FileReadStage)
    ensures !C.ReadFileSpec(fs, (_: TrustedStreamRequest) => StreamWriteResult(0, [], 0),
                            path, data, err, stage)
  {
  }

  // A stdin-shaped observation cannot satisfy a read-only open outcome.
  lemma WrongOpenReadConstructor(fs: FileSystem, path: Path, data: Bytes, err: int, stage: FileReadStage)
    ensures !C.OpenReadFileSpec(fs, (_: TrustedStreamRequest) => StreamReadStdinResult([], [], 0),
                                path, data, err, stage)
  {
  }

  // A file-shaped observation cannot satisfy any stdin-read outcome.
  lemma WrongStdinConstructor(before: Bytes, after: Bytes, data: Bytes, err: int)
    ensures !C.ReadStdinSpec(before, (_: TrustedStreamRequest) => StreamReadFileResult([], 0, ReadSucceeded),
                             after, data, err)
    ensures !C.ValidStreamObservation(StreamReadStdin(before), StreamReadFileResult([], 0, ReadSucceeded))
    ensures !C.StreamObservationsValid((_: TrustedStreamRequest) => StreamReadFileResult([], 0, ReadSucceeded))
  {
  }

  // A stdin-shaped observation cannot satisfy any stdout-write outcome.
  lemma WrongStdoutConstructor(before: Bytes, after: Bytes, requested: Bytes, committed: nat, err: int)
    ensures !C.WriteStdoutSpec(before, (_: TrustedStreamRequest) => StreamReadStdinResult([], [], 0),
                               after, requested, committed, err)
  {
  }

  // A file-shaped observation cannot satisfy any stderr-write outcome.
  lemma WrongStderrConstructor(before: Bytes, after: Bytes, requested: Bytes, committed: nat, err: int)
    ensures !C.WriteStderrSpec(before, (_: TrustedStreamRequest) => StreamReadFileResult([], 0, ReadSucceeded),
                               after, requested, committed, err)
  {
  }

  // A successful timestamp with negative nanoseconds has no full-contract outcome.
  lemma NegativeTimestampNanoseconds(ok: bool, sec: int, nsec: int)
    ensures !C.ParseTimestampSpec(map[TimestampParseRequest("202610230900", 0, 0) :=
                                        ParsedTimeResult(true, 0, -1)],
                                  "202610230900", 0, 0, ok, sec, nsec)
    ensures !C.TimeParseObservationsValid(map[TimestampParseRequest("202610230900", 0, 0) :=
                                                ParsedTimeResult(true, 0, -1)])
  {
  }

  // A successful date with one billion nanoseconds has no full-contract outcome.
  lemma OutOfRangeDateNanoseconds(ok: bool, sec: int, nsec: int)
    ensures !C.ParseDateSpec(map[DateParseRequest("now", 0, 0) :=
                                   ParsedTimeResult(true, 0, 1000000000)],
                             "now", 0, 0, ok, sec, nsec)
    ensures !C.TimeParseObservationsValid(map[DateParseRequest("now", 0, 0) :=
                                                ParsedTimeResult(true, 0, 1000000000)])
  {
  }

  // A successful file read retains the complete regular-file contents.
  lemma SuccessfulFileRead(fs: FileSystem, path: Path)
    requires C.ModeledReadFileResultFields(fs, path) == C.Result.Ok("abc")
  {
    ghost var observations := WithObservation(StreamReadFile(fs, path), StreamReadFileResult("abc", 0, ReadSucceeded));
    C.StreamObservationAdmitsRequest(observations, StreamReadFile(fs, path));
    assert C.ReadFileSpec(fs, observations, path, "abc", 0, ReadSucceeded);
  }

  // A native read failure retains a proper prefix and the ReadFailed stage.
  lemma PartialFileReadFailure(fs: FileSystem, path: Path)
    requires C.ModeledReadFileResultFields(fs, path) == C.Result.Ok("abc")
  {
    ghost var observations := WithObservation(StreamReadFile(fs, path), StreamReadFileResult("a", E.EIO, ReadFailed));
    C.StreamObservationAdmitsRequest(observations, StreamReadFile(fs, path));
    assert C.ReadFileSpec(fs, observations, path, "a", E.EIO, ReadFailed);
  }

  // A close failure remains a failure even after all file data was read.
  lemma CompleteFileReadCloseFailure(fs: FileSystem, path: Path)
    requires C.ModeledReadFileResultFields(fs, path) == C.Result.Ok("abc")
  {
    ghost var observations := WithObservation(StreamReadFile(fs, path), StreamReadFileResult("abc", E.EIO, CloseFailed));
    C.StreamObservationAdmitsRequest(observations, StreamReadFile(fs, path));
    assert C.ReadFileSpec(fs, observations, path, "abc", E.EIO, CloseFailed);
  }

  // A successful read-only probe admits no file-content consumption.
  lemma SuccessfulOpenReadProbe(fs: FileSystem, path: Path)
    requires C.ResolvePathForMetadataFields(fs, path, true).Ok?
  {
    ghost var observations := WithObservation(StreamOpenReadFile(fs, path), StreamReadFileResult([], 0, ReadSucceeded));
    C.StreamObservationAdmitsRequest(observations, StreamOpenReadFile(fs, path));
    assert C.OpenReadFileSpec(fs, observations, path, [], 0, ReadSucceeded);
  }

  // A read-only probe reports a close failure without inventing file data.
  lemma OpenReadProbeCloseFailure(fs: FileSystem, path: Path)
    requires C.ResolvePathForMetadataFields(fs, path, true).Ok?
  {
    ghost var observations := WithObservation(StreamOpenReadFile(fs, path), StreamReadFileResult([], E.EIO, CloseFailed));
    C.StreamObservationAdmitsRequest(observations, StreamOpenReadFile(fs, path));
    assert C.OpenReadFileSpec(fs, observations, path, [], E.EIO, CloseFailed);
  }

  // A complete stdin read is admitted by a globally valid provider.
  lemma SuccessfulStdinRead()
  {
    ghost var observations := WithObservation(StreamReadStdin("abc"), StreamReadStdinResult("abc", [], 0));
    C.StreamObservationAdmitsRequest(observations, StreamReadStdin("abc"));
    assert C.ReadStdinSpec("abc", observations, [], "abc", 0);
  }

  // A read error retains the consumed prefix and exact unread suffix.
  lemma PartialStdinReadFailure()
  {
    ghost var observations := WithObservation(StreamReadStdin("abc"), StreamReadStdinResult("a", "bc", E.EIO));
    C.StreamObservationAdmitsRequest(observations, StreamReadStdin("abc"));
    assert C.ReadStdinSpec("abc", observations, "bc", "a", E.EIO);
  }

  // A successful stdout write commits every requested byte.
  lemma SuccessfulStdoutWrite()
  {
    ghost var observations := WithObservation(StreamWriteStdout("x", "abc"), StreamWriteResult(3, "xabc", 0));
    C.StreamObservationAdmitsRequest(observations, StreamWriteStdout("x", "abc"));
    assert C.WriteStdoutSpec("x", observations, "xabc", "abc", 3, 0);
  }

  // A successful stderr write commits every requested byte.
  lemma SuccessfulStderrWrite()
  {
    ghost var observations := WithObservation(StreamWriteStderr("x", "abc"), StreamWriteResult(3, "xabc", 0));
    C.StreamObservationAdmitsRequest(observations, StreamWriteStderr("x", "abc"));
    assert C.WriteStderrSpec("x", observations, "xabc", "abc", 3, 0);
  }

  // A failed stdout write preserves exactly the two committed bytes.
  lemma PartialStdoutWriteFailure()
  {
    ghost var observations := WithObservation(StreamWriteStdout("x", "abc"), StreamWriteResult(2, "xab", E.EIO));
    C.StreamObservationAdmitsRequest(observations, StreamWriteStdout("x", "abc"));
    assert C.WriteStdoutSpec("x", observations, "xab", "abc", 2, E.EIO);
  }

  // Even an empty stderr write may fail with zero bytes committed.
  lemma EmptyStderrWriteFailure()
  {
    ghost var observations := WithObservation(StreamWriteStderr("x", []), StreamWriteResult(0, "x", E.EIO));
    C.StreamObservationAdmitsRequest(observations, StreamWriteStderr("x", []));
    assert C.WriteStderrSpec("x", observations, "x", [], 0, E.EIO);
  }

  // A normalized successful time parse is admitted by a finite validated map.
  lemma SuccessfulTimestampParse()
  {
    ghost var parses: C.ValidTimeParseObservations :=
      map[TimestampParseRequest("202610230900", 0, 0) := ParsedTimeResult(true, 1792746000, 999999999)];
    C.TimeParseObservationAdmitsRequest(parses, TimestampParseRequest("202610230900", 0, 0));
    assert C.ParseTimestampSpec(parses, "202610230900", 0, 0, true, 1792746000, 999999999);
  }

  // Failed date parses preserve arbitrary observed fields, including negative nanoseconds.
  lemma FailedDateParsePreservesFields()
  {
    ghost var parses: C.ValidTimeParseObservations :=
      map[DateParseRequest("invalid date", 0, 0) := ParsedTimeResult(false, 17, -1)];
    C.TimeParseObservationAdmitsRequest(parses, DateParseRequest("invalid date", 0, 0));
    assert C.ParseDateSpec(parses, "invalid date", 0, 0, false, 17, -1);
  }

  // An empty provider map admits the original default failure for missing requests.
  lemma MissingDateParseRequest()
  {
    ghost var parses: C.ValidTimeParseObservations := map[];
    C.TimeParseObservationAdmitsRequest(parses, DateParseRequest("missing", 0, 0));
    assert C.ParseDateSpec(parses, "missing", 0, 0, false, 0, 0);
  }
}
