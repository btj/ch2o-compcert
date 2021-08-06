From ch2o Require Export integer_coding.

Definition store := list (option Z).

Definition store_value_typed `{IntCoding K} oz :=
  match oz with
    None => True
  | Some z => int_typed z sintT
  end.

Definition store_typed `{IntCoding K} st :=
  Forall store_value_typed st.