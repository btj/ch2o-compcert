From ch2o Require Export architectures.

Definition A: architecture := {|
  arch_sizes := architectures.lp64;
  arch_big_endian := false;
  arch_char_signedness := integer_coding.Signed;
  arch_alloc_can_fail := false
|}.

Notation K := (arch_rank A).
