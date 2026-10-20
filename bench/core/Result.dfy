module Results {
  datatype Result<T, E> = Ok(v: T) | Err(e: E) {
    predicate IsFailure() { Err? }

    function Extract(): T
      requires Ok?
    { v }

    function PropagateFailure<U>(): Result<U, E>
      requires Err?
    { Err(e) }

  }
}
