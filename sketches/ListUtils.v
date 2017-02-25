Fixpoint last_error {A} (l : list A) :=
  match l with
  | cons x nil => Some x
  | cons _ ys => last_error ys
  | _ => None
  end.
