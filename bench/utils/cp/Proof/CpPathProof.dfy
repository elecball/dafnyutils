include "../Spec/CpSpec.dfy"
include "../Impl/CpPathCore.dfy"

module CpPathProof {
  import Spec = CpSpec
  import Paths = CpPathSpec
  import Core = CpPathCore
  import CliModel

  lemma TrimmedSummaryGivesRelation(path: string, trimmed: string)
    requires Core.TrimmedSummary(path,trimmed)
    ensures Spec.TrimmedPath(path,trimmed)
  {
    if |path| == 0 {
    } else if forall i :: 0 <= i < |path| ==> path[i] == '/' {
      assert Paths.SlashesOnly(path);
    } else {
      var end :| 0 < end <= |path| && trimmed == path[..end] &&
                 path[end-1] != '/' &&
                 forall i :: end <= i < |path| ==> path[i] == '/';
      var trailing := path[end..];
      assert Paths.PathWithoutTrailingSlashes(path,trimmed,trailing);
    }
  }

  lemma DigitCharacter(digit: nat)
    requires digit < 10
    ensures '0' <= Paths.DigitCharSpec(digit) <= '9'
    ensures (Paths.DigitCharSpec(digit) as int) - ('0' as int) == digit
    ensures digit > 0 ==> '1' <= Paths.DigitCharSpec(digit)
  {
  }

  lemma DecimalDigits(value: nat)
    ensures |Paths.DecimalNatSpec(value)| > 0
    ensures forall i | 0 <= i < |Paths.DecimalNatSpec(value)| :: '0' <= Paths.DecimalNatSpec(value)[i] <= '9'
    ensures value > 0 ==> '1' <= Paths.DecimalNatSpec(value)[0] <= '9'
    decreases value
  {
    reveal Paths.DecimalNatSpec();
    if value < 10 { DigitCharacter(value); }
    else {
      DecimalDigits(value / 10);
      DigitCharacter(value % 10);
    }
  }

  lemma DecimalAppend(value: nat, digit: nat)
    requires value > 0 && digit < 10
    ensures Paths.DecimalNatSpec(value*10+digit) == Paths.DecimalNatSpec(value)+[Paths.DigitCharSpec(digit)]
  {
    reveal Paths.DecimalNatSpec();
    assert (value*10+digit) / 10 == value;
    assert (value*10+digit) % 10 == digit;
  }

  lemma DecimalUnique(left: nat, right: nat)
    requires Paths.DecimalNatSpec(left) == Paths.DecimalNatSpec(right)
    ensures left == right
    decreases left+right
  {
    reveal Paths.DecimalNatSpec();
    DecimalDigits(left);
    DecimalDigits(right);
    if left < 10 && right < 10 {
      DigitCharacter(left);
      DigitCharacter(right);
    } else if left < 10 {
      DecimalDigits(right/10);
    } else if right < 10 {
      DecimalDigits(left/10);
    } else {
      DigitCharacter(left%10);
      DigitCharacter(right%10);
      var leftText,rightText := Paths.DecimalNatSpec(left),Paths.DecimalNatSpec(right);
      assert Paths.DecimalNatSpec(left/10) == leftText[..|leftText|-1];
      assert Paths.DecimalNatSpec(right/10) == rightText[..|rightText|-1];
      assert Paths.DigitCharSpec(left%10) == leftText[|leftText|-1];
      assert Paths.DigitCharSpec(right%10) == rightText[|rightText|-1];
      DecimalUnique(left/10,right/10);
    }
  }

  lemma NumberedVersionShape(base: string, name: string, version: nat)
    requires Spec.NumberedVersion(base,name,version)
    ensures |name| >= |base|+4
    ensures CliModel.HasPrefix(name,base+".~")
    ensures name[|name|-1] == '~'
    ensures '1' <= name[|base|+2] <= '9'
    ensures forall i | |base|+2 <= i < |name|-1 :: '0' <= name[i] <= '9'
    ensures name[|base|+2..|name|-1] == Paths.DecimalNatSpec(version)
  {
    DecimalDigits(version);
  }

  lemma RejectBackupLayout(base: string, name: string)
    requires |name| < |base|+4 || !CliModel.HasPrefix(name,base+".~") || name[|name|-1] != '~' || !('1' <= name[|base|+2] <= '9')
    ensures Spec.BackupVersion(base,name,0)
  {
    if exists version: nat :: Spec.NumberedVersion(base,name,version) {
      var version: nat :| Spec.NumberedVersion(base,name,version);
      NumberedVersionShape(base,name,version);
    }
  }

  lemma RejectBackupDigit(base: string, name: string, index: nat)
    requires |base|+2 <= index < |name|-1
    requires !('0' <= name[index] <= '9')
    ensures Spec.BackupVersion(base,name,0)
  {
    if exists version: nat :: Spec.NumberedVersion(base,name,version) {
      var version: nat :| Spec.NumberedVersion(base,name,version);
      NumberedVersionShape(base,name,version);
    }
  }

  lemma BackupVersionUnique(base: string, name: string, left: nat, right: nat)
    requires Spec.BackupVersion(base,name,left) && Spec.BackupVersion(base,name,right)
    ensures left == right
  {
    if left > 0 && right > 0 {
      NumberedVersionShape(base,name,left);
      NumberedVersionShape(base,name,right);
      DecimalUnique(left,right);
    }
  }

  lemma MaximumBackupAppend(entries: seq<Spec.DirectoryName>, base: string, maximum: nat,
                            next: Spec.DirectoryName, version: nat)
    requires Spec.MaximumBackup(entries,base,maximum)
    requires Spec.BackupVersion(base,next.name,version)
    ensures Spec.MaximumBackup(entries+[next],base,if version > maximum then version else maximum)
  {
    hide *;
    reveal Spec.MaximumBackup(), Spec.BackupVersion();
    var extended := entries+[next];
    var latest := if version > maximum then version else maximum;
    forall i: int, number: nat | 0 <= i < |extended| && Spec.NumberedVersion(base,extended[i].name,number)
      ensures number <= latest
    {
      if i < |entries| { assert extended[i] == entries[i]; }
      else {
        assert i == |entries| && extended[i] == next;
        assert number > 0 by { reveal Spec.NumberedVersion(); }
        assert Spec.BackupVersion(base,next.name,number);
        BackupVersionUnique(base,next.name,number,version);
      }
    }
    if latest > 0 {
      if version > maximum {
        assert Spec.NumberedVersion(base,extended[|entries|].name,latest);
      } else {
        var i :| 0 <= i < |entries| && Spec.NumberedVersion(base,entries[i].name,maximum);
        assert extended[i] == entries[i];
        assert Spec.NumberedVersion(base,extended[i].name,latest);
      }
    }
  }

  lemma ParentOffsetsWitness(path: string, offsets: seq<nat>)
    requires forall i | 0 <= i < |offsets| ::
               0 < offsets[i] < |path| && path[offsets[i]] == '/' && path[offsets[i]-1] != '/'
    requires forall i,j | 0 <= i < j < |offsets| :: offsets[i] < offsets[j]
    requires forall index | 0 < index < |path| && path[index] == '/' && path[index-1] != '/' :: index in offsets
    ensures Spec.ParentOffsets(path,offsets)
  {
    hide *;
    reveal Spec.ParentOffsets();
  }
}
