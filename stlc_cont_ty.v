(* Fixpoint transform3 { env R t T } (H : has_type env R t T) : B.tm := 
match H in (has_type _ _ _ _) return B.tm with 
  | t_true _ _ => B.ttrue
  | t_false _ _ => B.tfalse
  | t_var env R x T H => B.tvar x
  | t_abs env R t T1 T2 HT =>
    B.tabs (transform3 HT)

  | t_if env R cond tbranch ebranch T HTC HTT HTE =>
    B.tif (transform3 HTC) (transform3 HTT) (transform3 HTE)

  | t_app env R f t T1 T2 HF HT =>  
    B.tapp (transform3 HF) (transform3 HT)

  | _ => id_abs
end. *)
