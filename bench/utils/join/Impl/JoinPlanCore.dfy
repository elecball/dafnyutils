include "../Spec/JoinSpec.dfy"
include "JoinDataCore.dfy"

module JoinPlanCore {
  import Proof = JoinDataProof
  import S = JoinSchema
  import D = JoinDataSpec
  import Data = JoinDataCore
  import Spec = JoinSpec
  import BW = BenchWorld
  import BenchIO
  import C = IOContract

  method Usable(cmd: S.JoinCmdRaw, result: BW.IOResult<BW.Bytes>) returns (data: BW.Bytes)
    ensures Spec.UsableData(cmd,result,data)
  {
    var raw := C.ReadResultData(result);
    var p := |raw|;
    if Spec.ReadFailed(result) {
      while p > 0 && raw[p-1] != D.Delimiter(cmd)
        invariant 0 <= p <= |raw|
        invariant forall i: nat | p <= i < |raw| :: raw[i] != D.Delimiter(cmd)
        decreases p
      { p := p-1; }
    }
    data := raw[..p];
  }

  method Reads(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, tiles: seq<D.Tile>)
    returns (events: seq<D.Read>, cuts: seq<nat>)
    requires D.Tiles(cmd,left,right,tiles)
    ensures D.ReadLayout(cmd,left,right,tiles,events,cuts)
  {
    events := [D.Read(-1,1,0),D.Read(-1,2,0)];
    if cmd.header && |left|>0 { events := events+[D.Read(-2,1,1)]; }
    if cmd.header && |right|>0 { events := events+[D.Read(-2,2,1)]; }
    var initial := events;
    cuts := [|events|];
    var b: nat := 0;
    while b < |tiles|
      invariant b <= |tiles|
      invariant |events| >= |initial| == D.InitialCount(cmd,left,right)
      invariant events[..|initial|] == initial
      invariant |cuts| == b+1 && cuts[0] == |initial| && cuts[b] == |events|
      invariant forall k: nat | k < b :: D.ReadTile(tiles[k],k,events,cuts[k],cuts[k+1])
      decreases |tiles|-b
    {
      var t := tiles[b];
      Proof.TileBounds(cmd,left,right,t);
      var lcount := t.le-t.l;
      var rcount := t.re-t.r;
      var levents := seq(lcount,q requires 0 <= q < lcount => D.Read(b,1,t.l+q+1));
      var revents := seq(rcount,q requires 0 <= q < rcount => D.Read(b,2,t.r+q+1));
      ghost var oldEvents := events;
      ghost var oldCuts := cuts;
      events := events+(levents+revents);
      forall k: nat | k < b
        ensures D.ReadTile(tiles[k],k,events,cuts[k],cuts[k+1])
      { Proof.AppendReadTile(tiles[k],k,oldEvents,cuts[k],cuts[k+1],levents+revents); }
      assert D.ReadTile(t,b,events,cuts[b],|events|);
      cuts := cuts+[|events|]; b := b+1;
    }
    assert events[0] == D.Read(-1,1,0) && events[1] == D.Read(-1,2,0);
    assert cmd.header && |left|>0 ==> events[2] == D.Read(-2,1,1);
    assert cmd.header && |right|>0 ==> events[2+(if |left|>0 then 1 else 0)] == D.Read(-2,2,1) by { hide *; }
    assert D.ReadLayout(cmd,left,right,tiles,events,cuts);
  }

  method FirstWarning(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>,
                      tiles: seq<D.Tile>, events: seq<D.Read>, side: nat) returns (index: nat)
    ensures D.FirstWarning(cmd,left,right,tiles,events,side,index)
  {
    index := 0;
    while index < |events| && (events[index].side != side || !D.WarningCandidate(cmd,left,right,tiles,events[index]))
      invariant index <= |events|
      invariant forall i: nat | i < index :: events[i].side != side || !D.WarningCandidate(cmd,left,right,tiles,events[i])
      decreases |events|-index
    { index := index+1; }
  }

  method FirstFatal(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, tiles: seq<D.Tile>,
                    events: seq<D.Read>, w1: nat, w2: nat, failed1: bool, failed2: bool) returns (stop: nat)
    ensures D.FirstFatal(cmd,left,right,tiles,events,w1,w2,failed1,failed2,stop)
  {
    stop := 0;
    while stop < |events| && !D.Fatal(cmd,left,right,tiles,events,w1,w2,failed1,failed2,stop)
      invariant stop <= |events|
      invariant forall i: nat | i < stop :: !D.Fatal(cmd,left,right,tiles,events,w1,w2,failed1,failed2,i)
      decreases |events|-stop
    { stop := stop+1; }
  }

  method Warning(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, tiles: seq<D.Tile>,
                 events: seq<D.Read>, side: nat, index: nat) returns (message: BW.Bytes)
    requires |cmd.operands| == 2
    requires D.FirstWarning(cmd,left,right,tiles,events,side,index)
    ensures Spec.WarningDiagnostic(cmd,left,right,events,index,message)
  {
    message := [];
    if index == |events| { return; }
    var e := events[index];
    var lines := if side == 1 then left else right;
    var text := lines[e.index].text;
    var p: nat := 0;
    while p < |text| && p < 2147483647 && text[p] != '\0'
      invariant p <= |text| && p <= 2147483647
      invariant '\0' !in text[..p]
      decreases |text|-p
    { p := p+1; }
    var display := text[..p];
    assert Spec.DisplayPrefix(text,display);
    message := Spec.OrderError(cmd.operands[if side==1 then 0 else 1],e.index+1,display);
  }

  method {:isolate_assertions} TileOutput(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, t: D.Tile,
                                          auto1: nat, auto2: nat) returns (output: BW.Bytes)
    requires D.TileRelation(cmd,left,right,t)
    ensures D.TileOutput(cmd,left,right,t,auto1,auto2,output)
  {
    Proof.TileBounds(cmd,left,right,t);
    output := [];
    ghost var rows: seq<BW.Bytes> := [];
    ghost var cuts: seq<nat> := [0];
    var count := D.TileOutputCount(cmd,t);
    var q: nat := 0;
    while q < count
      invariant q <= count
      invariant |rows| == q && D.Concat(rows,output,cuts)
      invariant forall k: nat | k < q :: D.PrintedRow(cmd,left,right,t,auto1,auto2,k,rows[k])
      decreases count-q
    {
      var row: BW.Bytes;
      if D.Pair(t) {
        assert t.re-t.r > 0;
        Proof.QuotientBound(q,t.le-t.l,t.re-t.r);
        row := Data.Render(cmd,left[t.l+q/(t.re-t.r)],right[t.r+q%(t.re-t.r)],true,auto1,auto2);
      } else if t.l < t.le {
        row := Data.Render(cmd,left[t.l],D.Line([],[]),true,auto1,auto2);
      } else {
        row := Data.Render(cmd,D.Line([],[]),right[t.r],false,auto1,auto2);
      }
      assert D.PrintedRow(cmd,left,right,t,auto1,auto2,q,row) by { reveal D.PrintedRow(); }
      Proof.AppendConcat(rows,output,cuts,row);
      output := output+row; rows := rows+[row]; cuts := cuts+[|output|]; q := q+1;
    }
    assert D.TileOutputRows(cmd,left,right,t,auto1,auto2,output,rows,cuts);
    reveal D.TileOutput();
    assert D.TileOutput(cmd,left,right,t,auto1,auto2,output);
  }

  method Output(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, tiles: seq<D.Tile>,
                events: seq<D.Read>, readCuts: seq<nat>, stop: nat) returns (output: BW.Bytes)
    requires D.ReadLayout(cmd,left,right,tiles,events,readCuts)
    requires stop <= |events|
    ensures D.BodyOutput(cmd,left,right,tiles,events,readCuts,stop,output)
  {
    var auto1 := if |left|>0 then |left[0].fields| else 0;
    var auto2 := if |right|>0 then |right[0].fields| else 0;
    var head: BW.Bytes := [];
    if cmd.header && (|left|>0 || |right|>0) && stop >= 2 {
      head := Data.Render(cmd,if |left|>0 then left[0] else D.Line([],[]),
                          if |right|>0 then right[0] else D.Line([],[]),|left|>0,auto1,auto2);
    }
    output := head;
    ghost var parts: seq<BW.Bytes> := [head];
    ghost var cuts: seq<nat> := [0,|head|];
    var b: nat := 0;
    while b < |tiles|
      invariant b <= |tiles|
      invariant |parts| == b+1 && parts[0] == head && D.Concat(parts,output,cuts)
      invariant forall k: nat | k < b ::
                  if (if D.Pair(tiles[k]) then readCuts[k+1] else readCuts[k]) <= stop then
                    D.TileOutput(cmd,left,right,tiles[k],auto1,auto2,parts[k+1]) else parts[k+1] == []
      decreases |tiles|-b
    {
      var part: BW.Bytes := [];
      if (if D.Pair(tiles[b]) then readCuts[b+1] else readCuts[b]) <= stop {
        part := TileOutput(cmd,left,right,tiles[b],auto1,auto2);
      }
      Proof.AppendConcat(parts,output,cuts,part);
      output := output+part; parts := parts+[part]; cuts := cuts+[|output|]; b := b+1;
    }
    reveal D.BodyOutput();
    assert D.BodyOutput(cmd,left,right,tiles,events,readCuts,stop,output);
  }

  method Join(cmd: S.JoinCmdRaw, io: BenchIO.IO, first: BW.IOResult<BW.Bytes>, second: BW.IOResult<BW.Bytes>)
    returns (output: BW.Bytes, diagnostics: BW.Bytes, exit: int)
    requires |cmd.operands| == 2
    ensures Spec.JoinResult(cmd,first,second,output,diagnostics,exit)
  {
    var ldata := Usable(cmd,first); var rdata := Usable(cmd,second);
    var left := Data.Records(cmd,ldata); var right := Data.Records(cmd,rdata);
    var tiles := Data.Tiles(cmd,left,right);
    var events, readCuts := Reads(cmd,left,right,tiles);
    var w1 := FirstWarning(cmd,left,right,tiles,events,1);
    var w2 := FirstWarning(cmd,left,right,tiles,events,2);
    var stop := FirstFatal(cmd,left,right,tiles,events,w1,w2,Spec.ReadFailed(first),Spec.ReadFailed(second));
    output := Output(cmd,left,right,tiles,events,readCuts,stop);
    var message1 := Warning(cmd,left,right,tiles,events,1,w1);
    var message2 := Warning(cmd,left,right,tiles,events,2,w2);
    var warning1 := if w1 <= stop then message1 else [];
    var warning2 := if w2 <= stop then message2 else [];
    diagnostics := if w1 <= w2 then warning1+warning2 else warning2+warning1;
    var fatalOrder := cmd.order == S.CheckOrder && (stop == w1 || stop == w2) && stop < |events|;
    if stop < |events| {
      if !fatalOrder {
        var reason := io.GetCLocaleErrnoText(C.ResultErrno(if events[stop].side == 1 then first else second));
        diagnostics := diagnostics+Spec.ReadError(reason);
      }
    } else if Spec.CloseFailed(first) {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(first));
      diagnostics := diagnostics+Spec.FileError(cmd.operands[0],reason);
    } else if Spec.CloseFailed(second) {
      var reason := io.GetCLocaleErrnoText(C.ResultErrno(second));
      diagnostics := diagnostics+Spec.FileError(cmd.operands[1],reason);
    } else if w1 < |events| || w2 < |events| {
      diagnostics := diagnostics+Spec.DisorderSummary;
    }
    exit := if stop < |events| || Spec.CloseFailed(first) || Spec.CloseFailed(second) || w1 < |events| || w2 < |events| then 1 else 0;
    ghost var certificate := Spec.JoinWitnessData(ldata,rdata,left,right,tiles,events,readCuts,w1,w2,stop,message1,message2);
    assert Spec.JoinStructure(cmd,first,second,certificate) by { reveal Spec.JoinStructure(); }
    assert Spec.JoinWitness(cmd,first,second,certificate,output,diagnostics,exit) by { reveal Spec.JoinWitness(); }
    reveal Spec.JoinResult();
    assert Spec.JoinResult(cmd,first,second,output,diagnostics,exit);
  }
}
