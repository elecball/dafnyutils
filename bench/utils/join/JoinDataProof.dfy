include "JoinDataSpec.dfy"

module JoinDataProof {
  import JoinSchema
  import D = JoinDataSpec
  import BW = BenchWorld

  lemma TileBounds(cmd: JoinSchema.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>, t: D.Tile)
    requires D.TileRelation(cmd,left,right,t)
    ensures D.TileBounds(left,right,t)
  {
    reveal D.TileRelation();
  }

  lemma QuotientBound(q: nat, height: nat, width: nat)
    requires width > 0
    requires q < height*width
    ensures q/width < height
    ensures q%width < width
  {
    if q/width >= height {
      var difference := q/width-height;
      assert difference >= 0;
      assert difference*width >= 0;
      calc {
         height*width;
      <= height*width+difference*width;
      == (height+difference)*width;
      == (q/width)*width;
      <= q;
      }
    }
  }

  lemma AppendConcat(parts: seq<BW.Bytes>, output: BW.Bytes, cuts: seq<nat>, part: BW.Bytes)
    requires D.Concat(parts,output,cuts)
    ensures D.Concat(parts+[part],output+part,cuts+[|output+part|])
  {
    forall i: nat {:trigger (cuts+[|output+part|])[i]} | i < |parts|+1
      ensures (cuts+[|output+part|])[i] <= (cuts+[|output+part|])[i+1] <= |output+part| &&
              (output+part)[(cuts+[|output+part|])[i]..(cuts+[|output+part|])[i+1]] == (parts+[part])[i]
    {
      if i < |parts| {
        assert cuts[i] <= cuts[i+1] <= |output|;
        assert (output+part)[cuts[i]..cuts[i+1]] == output[cuts[i]..cuts[i+1]];
      }
    }
  }

  lemma AppendReadTile(t: D.Tile, b: nat, events: seq<D.Read>, start: nat, end: nat, tail: seq<D.Read>)
    requires D.ReadTile(t,b,events,start,end)
    ensures D.ReadTile(t,b,events+tail,start,end)
  {
    assert (events+tail)[start..start+t.le-t.l] == events[start..start+t.le-t.l];
    assert (events+tail)[start+t.le-t.l..end] == events[start+t.le-t.l..end];
  }

  lemma ExtendSegment(data: BW.Bytes, delimiter: char, line: D.Line, lo: nat, hi: nat, p: nat, q: nat)
    requires p <= q <= |data|
    requires D.RecordSegment(data[..p],delimiter,line,lo,hi)
    ensures D.RecordSegment(data[..q],delimiter,line,lo,hi)
  {
    assert lo < hi <= p;
    var e := hi-(if data[hi-1] == delimiter then 1 else 0);
    assert (data[..p])[lo..e] == data[lo..e] == (data[..q])[lo..e];
  }

  lemma AppendRecord(data: BW.Bytes, delimiter: char, lines: seq<D.Line>, cuts: seq<nat>,
                     p: nat, q: nat, next: nat, line: D.Line)
    requires p <= q <= |data|
    requires p < next <= |data|
    requires next == (if q < |data| then q+1 else q)
    requires q < |data| ==> data[q] == delimiter
    requires line.text == data[p..q] && delimiter !in line.text
    requires D.RecordCuts(data[..p],delimiter,lines,cuts)
    requires p > 0 ==> data[p-1] == delimiter
    ensures D.RecordCuts(data[..next],delimiter,lines+[line],cuts+[next])
  {
    var extended := lines+[line];
    var newCuts := cuts+[next];
    forall i: nat {:trigger extended[i]} | i < |extended|
      ensures D.RecordSegment(data[..next],delimiter,extended[i],newCuts[i],newCuts[i+1]) &&
              (i+1<|extended| ==> (data[..next])[newCuts[i+1]-1] == delimiter)
    {
      if i < |lines| {
        assert D.RecordSegment(data[..p],delimiter,lines[i],cuts[i],cuts[i+1]);
        ExtendSegment(data,delimiter,lines[i],cuts[i],cuts[i+1],p,next);
        if i+1 == |lines| { assert cuts[i+1] == p; }
      } else {
        if q == |data| {
          assert |line.text| > 0;
          assert line.text[|line.text|-1] == data[q-1];
          assert data[q-1] != delimiter;
        }
        assert D.RecordSegment(data[..next],delimiter,line,p,next);
      }
    }
  }
}
