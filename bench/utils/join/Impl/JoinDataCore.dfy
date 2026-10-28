include "../Spec/JoinDataSpec.dfy"
include "../Proof/JoinDataProof.dfy"

module JoinDataCore {
  import Proof = JoinDataProof
  import S = JoinSchema
  import D = JoinDataSpec
  import BW = BenchWorld

  method Fields(text: BW.Bytes, separator: int) returns (fields: seq<BW.Bytes>)
    ensures exists lo: seq<nat>, hi: seq<nat> :: D.Fields(text,separator,fields,lo,hi)
  {
    fields := [];
    ghost var lo: seq<nat> := [];
    ghost var hi: seq<nat> := [];
    if separator == -1 {
      var p: nat := 0;
      while p < |text|
        invariant p <= |text|
        invariant |fields| == |lo| == |hi|
        invariant forall i: nat | i < |fields| :: (lo[i] < hi[i] <= p && fields[i] == text[lo[i]..hi[i]] &&
                                                   (forall k: nat | lo[i] <= k < hi[i] :: !D.Blank(text[k])))
        invariant forall i: nat | i+1 < |fields| :: (hi[i] < lo[i+1] &&
                                                     (forall k: nat | hi[i] <= k < lo[i+1] :: D.Blank(text[k])))
        invariant forall k: nat | k < p :: (!D.Blank(text[k]) <==> exists i: nat :: i < |fields| && lo[i] <= k < hi[i])
        invariant |fields|>0 && p < |text| ==> D.Blank(text[p])
        invariant |fields|>0 ==> forall k: nat | hi[|fields|-1] <= k < p :: D.Blank(text[k])
        decreases |text|-p
      {
        var begin := p;
        while p < |text| && D.Blank(text[p])
          invariant begin <= p <= |text|
          invariant forall k: nat | begin <= k < p :: D.Blank(text[k])
          decreases |text|-p
        { p := p+1; }
        if p == |text| {
          assert D.Fields(text,separator,fields,lo,hi);
          return;
        }
        var q := p;
        while q < |text| && !D.Blank(text[q])
          invariant p <= q <= |text|
          invariant forall k: nat | p <= k < q :: !D.Blank(text[k])
          decreases |text|-q
        { q := q+1; }
        assert p < q;
        ghost var oldFields := fields;
        ghost var oldLo := lo;
        ghost var oldHi := hi;
        assert |oldFields| > 0 ==> oldHi[|oldFields|-1] < p;
        fields := fields+[text[p..q]]; lo := lo+[p]; hi := hi+[q];
        forall k: nat | k < q
          ensures !D.Blank(text[k]) <==> exists i: nat :: i < |fields| && lo[i] <= k < hi[i]
        {
          if k < begin && !D.Blank(text[k]) {
            var i: nat :| i < |oldFields| && oldLo[i] <= k < oldHi[i];
            assert lo[i] <= k < hi[i];
          } else if p <= k < q {
            assert lo[|oldFields|] <= k < hi[|oldFields|];
          }
        }
        p := q;
      }
      assert D.Fields(text,separator,fields,lo,hi);
    } else if |text| > 0 {
      var p: nat := 0;
      while true
        invariant p <= |text|
        invariant |fields| == |lo| == |hi|
        invariant forall i: nat | i < |fields| :: (lo[i] <= hi[i] < p && fields[i] == text[lo[i]..hi[i]] &&
                                                   (separator == 10 || forall k: nat | lo[i] <= k < hi[i] :: text[k] as int != separator))
        invariant |fields|>0 ==> lo[0] == 0 && hi[|fields|-1]+1 == p
        invariant |fields|==0 ==> p == 0
        invariant forall i: nat | i+1 < |fields| :: separator != 10 && text[hi[i]] as int == separator && lo[i+1] == hi[i]+1
        invariant forall i: nat | i < |fields| :: separator != 10 && text[hi[i]] as int == separator
        decreases |text|+1-p
      {
        var q := p;
        while q < |text| && (separator == 10 || text[q] as int != separator)
          invariant p <= q <= |text|
          invariant separator == 10 || forall k: nat | p <= k < q :: text[k] as int != separator
          decreases |text|-q
        { q := q+1; }
        fields := fields+[text[p..q]]; lo := lo+[p]; hi := hi+[q];
        if q == |text| {
          assert D.Fields(text,separator,fields,lo,hi);
          return;
        }
        p := q+1;
      }
    } else {
      assert D.Fields(text,separator,fields,lo,hi);
    }
  }

  method Records(cmd: S.JoinCmdRaw, data: BW.Bytes) returns (lines: seq<D.Line>)
    ensures D.Records(cmd,data,lines)
  {
    lines := [];
    ghost var cuts: seq<nat> := [0];
    var p: nat := 0;
    while p < |data|
      invariant p <= |data|
      invariant D.RecordCuts(data[..p],D.Delimiter(cmd),lines,cuts)
      invariant forall i: nat | i < |lines| :: D.FieldLine(cmd,lines[i])
      invariant p < |data| && p>0 ==> data[p-1] == D.Delimiter(cmd)
      decreases |data|-p
    {
      var q := p;
      while q < |data| && data[q] != D.Delimiter(cmd)
        invariant p <= q <= |data|
        invariant D.Delimiter(cmd) !in data[p..q]
        decreases |data|-q
      { q := q+1; }
      var text := data[p..q];
      var fields := Fields(text,cmd.separator);
      var next := if q < |data| then q+1 else q;
      assert p < next;
      assert D.FieldLine(cmd,D.Line(text,fields));
      Proof.AppendRecord(data,D.Delimiter(cmd),lines,cuts,p,q,next,D.Line(text,fields));
      lines := lines+[D.Line(text,fields)]; cuts := cuts+[next];
      p := next;
    }
    assert data[..p] == data;
    assert D.RecordCuts(data,D.Delimiter(cmd),lines,cuts);
    assert D.Records(cmd,data,lines);
  }

  method Compare(a: BW.Bytes, b: BW.Bytes) returns (cmp: int)
    ensures -1 <= cmp <= 1
    ensures cmp == 0 <==> a == b
    ensures cmp < 0 ==> D.Less(a,b)
    ensures cmp > 0 ==> D.Less(b,a)
  {
    var i: nat := 0;
    while i < |a| && i < |b| && a[i] == b[i]
      invariant i <= |a| && i <= |b|
      invariant a[..i] == b[..i]
      decreases |a|+|b|-2*i
    { i := i+1; }
    if i == |a| && i == |b| { cmp := 0; }
    else if i == |a| || (i < |a| && i < |b| && a[i] < b[i]) {
      cmp := -1;
      assert D.Less(a,b);
      assert a != b;
    } else {
      cmp := 1;
      assert D.Less(b,a);
      assert a != b;
    }
  }

  method Tiles(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>) returns (tiles: seq<D.Tile>)
    ensures D.Tiles(cmd,left,right,tiles)
  {
    tiles := [];
    var l := D.Start(cmd,left); var r := D.Start(cmd,right);
    while l < |left| || r < |right|
      invariant l <= |left| && r <= |right|
      invariant if |tiles|==0 then (l == D.Start(cmd,left) && r == D.Start(cmd,right))
                else (tiles[0].l == D.Start(cmd,left) && tiles[0].r == D.Start(cmd,right) &&
                      tiles[|tiles|-1].le == l && tiles[|tiles|-1].re == r)
      invariant forall b: nat | b < |tiles| :: D.TileRelation(cmd,left,right,tiles[b])
      invariant forall b: nat | b+1 < |tiles| :: tiles[b].le == tiles[b+1].l && tiles[b].re == tiles[b+1].r
      decreases |left|+|right|-l-r
    {
      var le := l; var re := r;
      var cmp := if l == |left| then 1 else -1;
      if l < |left| && r < |right| {
        cmp := Compare(D.Key(left[l],cmd.field1,cmd.ignoreCase),D.Key(right[r],cmd.field2,cmd.ignoreCase));
      }
      if cmp < 0 { le := l+1; }
      else if cmp > 0 { re := r+1; }
      else {
        le := l+1;
        while le < |left| && D.Key(left[le],cmd.field1,cmd.ignoreCase) == D.Key(left[l],cmd.field1,cmd.ignoreCase)
          invariant l < le <= |left|
          invariant forall i: nat | l <= i < le :: D.Key(left[i],cmd.field1,cmd.ignoreCase) == D.Key(left[l],cmd.field1,cmd.ignoreCase)
          decreases |left|-le
        { le := le+1; }
        re := r+1;
        while re < |right| && D.Key(right[re],cmd.field2,cmd.ignoreCase) == D.Key(right[r],cmd.field2,cmd.ignoreCase)
          invariant r < re <= |right|
          invariant forall i: nat | r <= i < re :: D.Key(right[i],cmd.field2,cmd.ignoreCase) == D.Key(right[r],cmd.field2,cmd.ignoreCase)
          decreases |right|-re
        { re := re+1; }
      }
      var t := D.Tile(l,r,le,re);
      assert D.TileRelation(cmd,left,right,t) by { reveal D.TileRelation(); }
      tiles := tiles+[t]; l := le; r := re;
    }
  }

  method Render(cmd: S.JoinCmdRaw, left: D.Line, right: D.Line, hasLeft: bool,
                auto1: nat, auto2: nat) returns (output: BW.Bytes)
    ensures D.Printed(cmd,left,right,hasLeft,auto1,auto2,output)
  {
    output := [];
    ghost var cuts: seq<nat> := [0];
    ghost var parts: seq<BW.Bytes> := [];
    var count := D.OutputCount(cmd,left,right,auto1,auto2);
    var i: nat := 0;
    while i < count
      invariant i <= count
      invariant |parts| == i && D.Concat(parts,output,cuts)
      invariant forall k: nat | k < i :: (parts[k] == D.SelectedField(cmd,left,right,hasLeft,auto1,auto2,k)+
                                                      (if k+1 == count then [D.Delimiter(cmd)] else cmd.outputSeparator))
      decreases count-i
    {
      var field := D.SelectedField(cmd,left,right,hasLeft,auto1,auto2,i);
      var part := field+(if i+1 == count then [D.Delimiter(cmd)] else cmd.outputSeparator);
      Proof.AppendConcat(parts,output,cuts,part);
      output := output+part; parts := parts+[part]; cuts := cuts+[|output|]; i := i+1;
    }
    assert D.Fragment(cmd,left,right,hasLeft,auto1,auto2,output,cuts);
    reveal D.Printed();
  }
}
