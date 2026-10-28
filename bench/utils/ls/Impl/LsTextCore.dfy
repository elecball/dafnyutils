include "../Spec/LsSpec.dfy"

module LsTextCore {
  import BenchWorld
  import Schema = LsSchema
  import Time = LsTime
  import opened Model = LsSpec

  function MaximumWidth(values: set<nat>): (maximum: nat)
    ensures MaximumWidth(values) == Model.MaximumWidth(values)
    ensures values == {} ==> maximum == 0
    ensures values != {} ==> maximum in values
    ensures forall value: nat | value in values :: value <= maximum
  {
    Model.MaximumWidth(values)
  } by method {
    if values == {} {
      return 0;
    }
    var member: nat :| member in values;
    maximum := member;
    var remaining := values - {member};
    while remaining != {}
      invariant remaining <= values
      invariant maximum in values
      invariant forall value: nat | value in values - remaining :: value <= maximum
      decreases |remaining|
    {
      ghost var beforeRemaining := remaining;
      ghost var beforeMaximum := maximum;
      var value: nat :| value in remaining;
      remaining := remaining - {value};
      if maximum < value {
        maximum := value;
      }
      assert beforeMaximum <= maximum;
      assert forall item: nat | item in values - remaining :: item <= maximum by {
        forall item: nat | item in values - remaining
          ensures item <= maximum
        {
          if item != value {
            assert item in values - beforeRemaining;
            assert item <= beforeMaximum;
          }
        }
      }
    }
    ghost var modeled := Model.MaximumWidth(values);
    assert modeled in values;
    assert modeled in values - remaining;
    assert modeled <= maximum;
    assert maximum <= modeled;
    return maximum;
  }

  function StatusWidthsSpec(cmd: Schema.LsCmd, statuses: set<BenchWorld.FileStatus>): ColumnWidths
    ensures StatusWidthsSpec(cmd, statuses) == Model.StatusWidthsSpec(cmd, statuses)
  {
    ColumnWidths(
      MaximumWidth(set status <- statuses :: |Time.NatText(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize))|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.linkCount)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.ownership.uid)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.ownership.gid)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(DisplayedFileSizeSpec(status.storage.size, cmd.fileSizeBlockSize))|))
  }

  function ObservationWidthsSpec(cmd: Schema.LsCmd, observations: seq<EntryObservation>): ColumnWidths
    ensures ObservationWidthsSpec(cmd, observations) == Model.ObservationWidthsSpec(cmd, observations)
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

  function OperandWidthsSpec(cmd: Schema.LsCmd, observations: seq<OperandObservation>): ColumnWidths
    ensures OperandWidthsSpec(cmd, observations) == Model.OperandWidthsSpec(cmd, observations)
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

}
