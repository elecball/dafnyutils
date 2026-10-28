include "JoinSchema.dfy"

module JoinDataSpec {
  import S = JoinSchema
  import BW = BenchWorld

  datatype Line = Line(text: BW.Bytes, fields: seq<BW.Bytes>)
  datatype Tile = Tile(l: nat, r: nat, le: nat, re: nat)
  datatype Read = Read(tile: int, side: nat, index: nat)

  function Delimiter(cmd: S.JoinCmdRaw): char { if cmd.zero then '\0' else '\n' }
  function Blank(c: char): bool { c in " \t\n" }
  function FoldByte(c: char, ignore: bool): char {
    if ignore && 'a' <= c <= 'z' then (c as int - 32) as char else c
  }
  function Fold(bytes: BW.Bytes, ignore: bool): BW.Bytes {
    seq(|bytes|, i requires 0 <= i < |bytes| => FoldByte(bytes[i], ignore))
  }
  function Key(line: Line, index: nat, ignore: bool): BW.Bytes {
    Fold(if index < |line.fields| then line.fields[index] else [], ignore)
  }
  predicate Less(a: BW.Bytes, b: BW.Bytes) {
    exists k: nat :: k <= |a| && k <= |b| && a[..k] == b[..k] &&
                     (k == |a| < |b| || (k < |a| && k < |b| && a[k] < b[k]))
  }

  ghost predicate Fields(line: BW.Bytes, separator: int, fields: seq<BW.Bytes>, lo: seq<nat>, hi: seq<nat>) {
    |fields| == |lo| == |hi| &&
    (forall i: nat | i < |fields| :: lo[i] <= hi[i] <= |line| && fields[i] == line[lo[i]..hi[i]]) &&
    if separator == -1 then
      (forall i: nat | i < |fields| :: lo[i] < hi[i] &&
                                       (forall p: nat | lo[i] <= p < hi[i] :: !Blank(line[p]))) &&
      (forall p: nat | p < |line| ::
         (!Blank(line[p]) <==> exists i: nat :: i < |fields| && lo[i] <= p < hi[i])) &&
      (forall i: nat | i + 1 < |fields| :: hi[i] < lo[i+1] &&
                                           (forall p: nat | hi[i] <= p < lo[i+1] :: Blank(line[p])))
    else if |line| == 0 then |fields| == 0
    else
      |fields| > 0 && lo[0] == 0 && hi[|fields|-1] == |line| &&
      (forall i: nat | i + 1 < |fields| :: hi[i] < |line| &&
                                           separator != 10 && line[hi[i]] as int == separator && lo[i+1] == hi[i]+1) &&
      (forall i: nat | i < |fields| ::
         separator == 10 || (forall p: nat | lo[i] <= p < hi[i] :: line[p] as int != separator)) &&
      (separator == 10 ==> |fields| == 1)
  }
  ghost predicate FieldLine(cmd: S.JoinCmdRaw, line: Line) {
    exists lo: seq<nat>, hi: seq<nat> :: Fields(line.text, cmd.separator, line.fields, lo, hi)
  }
  ghost predicate RecordSegment(data: BW.Bytes, delimiter: char, line: Line, lo: nat, hi: nat) {
    lo < hi <= |data| &&
    line.text == data[lo..hi-(if data[hi-1] == delimiter then 1 else 0)] && delimiter !in line.text
  }
  ghost predicate RecordCuts(data: BW.Bytes, delimiter: char, lines: seq<Line>, cuts: seq<nat>) {
    |cuts| == |lines|+1 && cuts[0] == 0 && cuts[|lines|] == |data| &&
    forall i: nat {:trigger lines[i]} | i < |lines| :: RecordSegment(data,delimiter,lines[i],cuts[i],cuts[i+1]) &&
                                                       (i+1<|lines| ==> data[cuts[i+1]-1] == delimiter)
  }
  ghost predicate Records(cmd: S.JoinCmdRaw, data: BW.Bytes, lines: seq<Line>) {
    (exists cuts: seq<nat> :: RecordCuts(data, Delimiter(cmd), lines, cuts)) &&
    forall i: nat | i < |lines| :: FieldLine(cmd, lines[i])
  }
  function Start(cmd: S.JoinCmdRaw, lines: seq<Line>): nat { if cmd.header && |lines| > 0 then 1 else 0 }
  function MainTile(t: Tile, left: seq<Line>, right: seq<Line>): bool { t.l < |left| && t.r < |right| }
  function Pair(t: Tile): bool { t.l < t.le && t.r < t.re }
  ghost predicate TileBounds(left: seq<Line>, right: seq<Line>, t: Tile) {
    t.l <= t.le <= |left| && t.r <= t.re <= |right| && t.l+t.r < t.le+t.re
  }
  opaque ghost predicate TileRelation(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, t: Tile) {
    TileBounds(left,right,t) &&
    if Pair(t) then
      Key(left[t.l],cmd.field1,cmd.ignoreCase) == Key(right[t.r],cmd.field2,cmd.ignoreCase) &&
      (forall i: nat | t.l <= i < t.le :: Key(left[i],cmd.field1,cmd.ignoreCase) == Key(left[t.l],cmd.field1,cmd.ignoreCase)) &&
      (forall i: nat | t.r <= i < t.re :: Key(right[i],cmd.field2,cmd.ignoreCase) == Key(right[t.r],cmd.field2,cmd.ignoreCase)) &&
      (t.le < |left| ==> Key(left[t.le],cmd.field1,cmd.ignoreCase) != Key(left[t.l],cmd.field1,cmd.ignoreCase)) &&
      (t.re < |right| ==> Key(right[t.re],cmd.field2,cmd.ignoreCase) != Key(right[t.r],cmd.field2,cmd.ignoreCase))
    else if t.l < t.le then
      t.le == t.l+1 && t.re == t.r &&
      (t.r == |right| || Less(Key(left[t.l],cmd.field1,cmd.ignoreCase),Key(right[t.r],cmd.field2,cmd.ignoreCase)))
    else
      t.re == t.r+1 && t.le == t.l &&
      (t.l == |left| || Less(Key(right[t.r],cmd.field2,cmd.ignoreCase),Key(left[t.l],cmd.field1,cmd.ignoreCase)))
  }
  ghost predicate Tiles(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, tiles: seq<Tile>) {
    (if |tiles| == 0 then (Start(cmd,left) == |left| && Start(cmd,right) == |right|)
     else (tiles[0].l == Start(cmd,left) && tiles[0].r == Start(cmd,right) &&
           tiles[|tiles|-1].le == |left| && tiles[|tiles|-1].re == |right|)) &&
    (forall b: nat | b < |tiles| :: TileRelation(cmd,left,right,tiles[b])) &&
    (forall b: nat | b+1 < |tiles| :: tiles[b].le == tiles[b+1].l && tiles[b].re == tiles[b+1].r)
  }

  function FieldValue(fields: seq<BW.Bytes>, index: nat, filler: BW.Bytes): BW.Bytes {
    if index < |fields| && fields[index] != [] then fields[index] else filler
  }
  function CountOther(count: nat, joinField: nat): nat { count - (if joinField < count then 1 else 0) }
  function OutputCount(cmd: S.JoinCmdRaw, left: Line, right: Line, auto1: nat, auto2: nat): nat {
    if |cmd.format| > 0 then |cmd.format| else (1 +
                                                CountOther(if cmd.autoformat then auto1 else |left.fields|,cmd.field1) +
                                                CountOther(if cmd.autoformat then auto2 else |right.fields|,cmd.field2))
  }
  function SelectedField(cmd: S.JoinCmdRaw, left: Line, right: Line, hasLeft: bool,
                         auto1: nat, auto2: nat, i: nat): BW.Bytes
    requires i < OutputCount(cmd,left,right,auto1,auto2)
  {
    var key := if hasLeft then FieldValue(left.fields,cmd.field1,cmd.filler)
               else FieldValue(right.fields,cmd.field2,cmd.filler);
    if |cmd.format| > 0 then
      var f := cmd.format[i];
      if f.file == 0 then key else FieldValue(if f.file == 1 then left.fields else right.fields,f.index,cmd.filler)
    else if i == 0 then key
    else
      var n := CountOther(if cmd.autoformat then auto1 else |left.fields|,cmd.field1);
      var j := if i <= n then i-1 else i-n-1;
      var field := if i <= n then cmd.field1 else cmd.field2;
      FieldValue(if i <= n then left.fields else right.fields,if j < field then j else j+1,cmd.filler)
  }
  ghost predicate Fragment(cmd: S.JoinCmdRaw, left: Line, right: Line, hasLeft: bool,
                           auto1: nat, auto2: nat, output: BW.Bytes, cuts: seq<nat>) {
    var count := OutputCount(cmd,left,right,auto1,auto2);
    |cuts| == count+1 && cuts[0] == 0 && cuts[count] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < count :: cuts[i] <= cuts[i+1] <= |output| &&
                                                    output[cuts[i]..cuts[i+1]] == SelectedField(cmd,left,right,hasLeft,auto1,auto2,i) +
                                                    (if i+1 == count then [Delimiter(cmd)] else cmd.outputSeparator)
  }
  opaque ghost predicate Printed(cmd: S.JoinCmdRaw, left: Line, right: Line, hasLeft: bool,
                                 auto1: nat, auto2: nat, output: BW.Bytes) {
    exists cuts: seq<nat> :: Fragment(cmd,left,right,hasLeft,auto1,auto2,output,cuts)
  }

  function InitialCount(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>): nat {
    2 + (if cmd.header && |left| > 0 then 1 else 0) + (if cmd.header && |right| > 0 then 1 else 0)
  }
  function ReadCount(t: Tile): nat
    requires t.l <= t.le && t.r <= t.re
  { t.le-t.l+t.re-t.r }
  ghost predicate ReadTile(t: Tile, b: nat, events: seq<Read>, start: nat, end: nat) {
    t.l <= t.le && t.r <= t.re && start <= end <= |events| && end == start+ReadCount(t) &&
    events[start..start+t.le-t.l] == seq(t.le-t.l,q requires 0 <= q < t.le-t.l => Read(b,1,t.l+q+1)) &&
    events[start+t.le-t.l..end] == seq(t.re-t.r,q requires 0 <= q < t.re-t.r => Read(b,2,t.r+q+1))
  }
  ghost predicate ReadLayout(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>,
                             tiles: seq<Tile>, events: seq<Read>, cuts: seq<nat>) {
    Tiles(cmd,left,right,tiles) && |events| >= InitialCount(cmd,left,right) &&
    events[0] == Read(-1,1,0) && events[1] == Read(-1,2,0) &&
    (cmd.header && |left| > 0 ==> events[2] == Read(-2,1,1)) &&
    (cmd.header && |right| > 0 ==> events[2+(if |left|>0 then 1 else 0)] == Read(-2,2,1)) &&
    |cuts| == |tiles|+1 && cuts[0] == InitialCount(cmd,left,right) && cuts[|tiles|] == |events| &&
    (forall b: nat | b < |tiles| :: ReadTile(tiles[b],b,events,cuts[b],cuts[b+1]))
  }
  function Descent(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, e: Read): bool {
    var lines := if e.side == 1 then left else right;
    var field := if e.side == 1 then cmd.field1 else cmd.field2;
    e.tile >= 0 && 0 < e.index < |lines| &&
    Key(lines[e.index-1],field,cmd.ignoreCase) != Key(lines[e.index],field,cmd.ignoreCase) &&
    Less(Key(lines[e.index],field,cmd.ignoreCase),Key(lines[e.index-1],field,cmd.ignoreCase))
  }
  predicate WarningCandidate(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, tiles: seq<Tile>, e: Read) {
    cmd.order != S.NoCheckOrder && Descent(cmd,left,right,e) &&
    (cmd.order == S.CheckOrder || exists b: nat :: (b < |tiles| && b < e.tile &&
                                                    MainTile(tiles[b],left,right) && !Pair(tiles[b])))
  }
  ghost predicate FirstWarning(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>,
                               tiles: seq<Tile>, events: seq<Read>, side: nat, index: nat) {
    index <= |events| &&
    (index < |events| ==> events[index].side == side && WarningCandidate(cmd,left,right,tiles,events[index])) &&
    forall i: nat | i < index :: events[i].side != side || !WarningCandidate(cmd,left,right,tiles,events[i])
  }
  // A nonprinting tail is scanned until its first disorder warning. A warning
  // issued during the merge still permits the first subsequent tail read.
  predicate Enabled(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>,
                    tiles: seq<Tile>, events: seq<Read>, w1: nat, w2: nat, i: nat)
    requires i < |events|
  {
    var e := events[i];
    e.tile < 0 || e.tile >= |tiles| || MainTile(tiles[e.tile],left,right) ||
    (if e.side == 1 then cmd.unpaired1 else cmd.unpaired2) ||
    (cmd.order != S.NoCheckOrder &&
     (forall j: nat | j < i :: events[j].tile < 0 || events[j].tile >= |tiles| ||
                               MainTile(tiles[events[j].tile],left,right) || events[j].side != e.side ||
                               (if e.side == 1 then w1 > j else w2 > j)) &&
     !(w1 < i && w2 < i))
  }
  predicate Fatal(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, tiles: seq<Tile>,
                  events: seq<Read>, w1: nat, w2: nat, failed1: bool, failed2: bool, i: nat)
    requires i < |events|
  {
    Enabled(cmd,left,right,tiles,events,w1,w2,i) &&
    ((cmd.order == S.CheckOrder && (i == w1 || i == w2)) ||
     (if events[i].side == 1 then failed1 && events[i].index == |left|
      else failed2 && events[i].index == |right|))
  }
  ghost predicate FirstFatal(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, tiles: seq<Tile>,
                             events: seq<Read>, w1: nat, w2: nat, failed1: bool, failed2: bool, stop: nat) {
    stop <= |events| && (stop < |events| ==> Fatal(cmd,left,right,tiles,events,w1,w2,failed1,failed2,stop)) &&
    forall i: nat | i < stop :: !Fatal(cmd,left,right,tiles,events,w1,w2,failed1,failed2,i)
  }
  ghost predicate Concat(parts: seq<BW.Bytes>, output: BW.Bytes, cuts: seq<nat>) {
    |cuts| == |parts|+1 && cuts[0] == 0 && cuts[|parts|] == |output| &&
    forall i: nat {:trigger cuts[i]} | i < |parts| :: cuts[i] <= cuts[i+1] <= |output| &&
                                                      output[cuts[i]..cuts[i+1]] == parts[i]
  }
  function TileOutputCount(cmd: S.JoinCmdRaw, t: Tile): nat {
    if Pair(t) then if cmd.paired then (t.le-t.l)*(t.re-t.r) else 0
    else if (if t.l < t.le then cmd.unpaired1 else cmd.unpaired2) then 1 else 0
  }
  opaque ghost predicate PrintedRow(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, t: Tile,
                                    auto1: nat, auto2: nat, q: nat, row: BW.Bytes) {
    TileRelation(cmd,left,right,t) && TileBounds(left,right,t) && q < TileOutputCount(cmd,t) &&
    if Pair(t) then
      q/(t.re-t.r) < t.le-t.l && q%(t.re-t.r) < t.re-t.r &&
      Printed(cmd,left[t.l+q/(t.re-t.r)],right[t.r+q%(t.re-t.r)],true,auto1,auto2,row)
    else if t.l < t.le then Printed(cmd,left[t.l],Line([],[]),true,auto1,auto2,row)
    else Printed(cmd,Line([],[]),right[t.r],false,auto1,auto2,row)
  }
  ghost predicate TileOutputRows(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, t: Tile,
                                 auto1: nat, auto2: nat, output: BW.Bytes, rows: seq<BW.Bytes>, cuts: seq<nat>) {
    TileRelation(cmd,left,right,t) &&
    |rows| == TileOutputCount(cmd,t) && Concat(rows,output,cuts) &&
    forall q: nat | q < |rows| :: PrintedRow(cmd,left,right,t,auto1,auto2,q,rows[q])
  }
  opaque ghost predicate TileOutput(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, t: Tile,
                                    auto1: nat, auto2: nat, output: BW.Bytes) {
    exists rows: seq<BW.Bytes>, cuts: seq<nat> :: TileOutputRows(cmd,left,right,t,auto1,auto2,output,rows,cuts)
  }
  opaque ghost predicate BodyOutput(cmd: S.JoinCmdRaw, left: seq<Line>, right: seq<Line>, tiles: seq<Tile>,
                                    events: seq<Read>, readCuts: seq<nat>, stop: nat, output: BW.Bytes) {
    ReadLayout(cmd,left,right,tiles,events,readCuts) && stop <= |events| &&
    exists parts: seq<BW.Bytes>, cuts: seq<nat> ::
      |parts| == |tiles|+1 && Concat(parts,output,cuts) &&
      (if cmd.header && (|left|>0 || |right|>0) && stop >= 2 then
         Printed(cmd,if |left|>0 then left[0] else Line([],[]),if |right|>0 then right[0] else Line([],[]),
                 |left|>0,if |left|>0 then |left[0].fields| else 0,if |right|>0 then |right[0].fields| else 0,parts[0])
       else parts[0] == []) &&
      forall b: nat | b < |tiles| ::
        (if (if Pair(tiles[b]) then readCuts[b+1] else readCuts[b]) <= stop then
           TileOutput(cmd,left,right,tiles[b],if |left|>0 then |left[0].fields| else 0,
                      if |right|>0 then |right[0].fields| else 0,parts[b+1])
         else parts[b+1] == [])
  }
}
