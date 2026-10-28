include "../Spec/RealpathSpec.dfy"

module RealpathPathProof {
  import Spec = RealpathSpec
  import S = RealpathSchema
  import BW = BenchWorld
  import R = Results

  lemma Directory(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
                  existence: S.Existence, directory: string, suffix: string)
    ensures Spec.Meaning(fs, failures, existence, S.Anchor(directory), suffix,
                         Spec.Ok(directory), Spec.DirectoryMeaning)
  {
    hide *;
    reveal Spec.Meaning();
  }

  lemma Child(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
              existence: S.Existence, parent: S.PathExpr, name: string, suffix: string,
              parentResult: Spec.PathResult, result: Spec.PathResult,
              prior: Spec.MeaningProof, rule: Spec.ComponentProof)
    requires Spec.Meaning(fs, failures, existence, parent, "/" + name + suffix, parentResult, prior)
    requires Spec.ComponentMeaning(fs, failures, existence, parentResult, name, suffix, result, rule)
    ensures Spec.Meaning(fs, failures, existence, S.Child(parent, name), suffix,
                         result, Spec.ChildMeaning(prior, parentResult, rule))
  {
    hide *;
    reveal Spec.Meaning();
  }

  lemma Failure(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
                existence: S.Existence, parent: Spec.PathResult, name: string, suffix: string)
    requires !parent.Ok?
    ensures Spec.ComponentMeaning(fs, failures, existence, parent, name, suffix,
                                  parent, Spec.InheritedFailure)
  {
    hide *;
    reveal Spec.ComponentMeaning();
  }

  lemma Same(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
             existence: S.Existence, parent: Spec.PathResult, name: string, suffix: string)
    requires parent.Ok? && (name == "" || name == ".")
    ensures Spec.ComponentMeaning(fs, failures, existence, parent, name, suffix,
                                  parent, Spec.SameDirectory)
  {
    hide *;
    reveal Spec.ComponentMeaning();
  }

  lemma Up(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
           existence: S.Existence, parent: string, name: string, suffix: string, value: string)
    requires name == ".." && Spec.ParentPath(parent, value)
    ensures Spec.ComponentMeaning(fs, failures, existence, Spec.Ok(parent), name, suffix,
                                  Spec.Ok(value), Spec.ParentDirectory)
  {
    hide *;
    reveal Spec.ComponentMeaning();
  }

  lemma Name(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
             existence: S.Existence, parent: string, name: string, suffix: string,
             result: Spec.PathResult, status: Spec.Status)
    requires name != "" && name != "." && name != ".."
    requires Spec.OrdinaryMeaning(fs, failures, existence, parent, name, suffix, result, status)
    ensures Spec.ComponentMeaning(fs, failures, existence, Spec.Ok(parent), name, suffix,
                                  result, Spec.Ordinary(status))
  {
    hide *;
    reveal Spec.ComponentMeaning();
  }

  lemma SetCardinality<T>(before: set<T>, after: set<T>)
    requires before <= after
    ensures |before| <= |after|
  {
    assert after == before + (after - before);
    assert before !! (after - before);
    assert |after| == |before| + |after - before|;
  }

  lemma PhysicalDirectory(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
                          observations: BW.StatusTimeObservations, cursor: nat, existence: S.Existence,
                          directory: string, suffix: string, history: Spec.History)
    ensures Spec.PhysicalMeaning(fs, failures, observations, cursor, cursor, existence,
                                 S.Anchor(directory), suffix, history, history, Spec.Ok(directory), Spec.PhysicalDirectory)
  {
    hide *;
    reveal Spec.PhysicalMeaning();
  }

  lemma PhysicalChild(fs: BW.FileSystem, failures: (BW.NativeFailureRequest) -> int,
                      observations: BW.StatusTimeObservations, first: nat, middle: nat, last: nat,
                      existence: S.Existence, parent: S.PathExpr, name: string, suffix: string,
                      before: Spec.History, parentHistory: Spec.History, after: Spec.History,
                      parentResult: Spec.PathResult, result: Spec.PathResult,
                      prior: Spec.PhysicalProof, rule: Spec.PhysicalRule)
    requires Spec.PhysicalMeaning(fs, failures, observations, first, middle, existence,
                                  parent, "/" + name + suffix, before, parentHistory, parentResult, prior)
    requires Spec.PhysicalComponent(fs, failures, observations, middle, last, existence,
                                    parentResult, name, suffix, parentHistory, after, result, rule)
    ensures Spec.PhysicalMeaning(fs, failures, observations, first, last, existence,
                                 S.Child(parent, name), suffix, before, after, result,
                                 Spec.PhysicalChild(prior, parentResult, parentHistory, middle, rule))
  {
    hide *;
    reveal Spec.PhysicalMeaning();
  }
}
