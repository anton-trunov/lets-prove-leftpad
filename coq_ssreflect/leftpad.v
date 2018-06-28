(* TODO: move from seq to n.-tuple *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LeftPad.

(* [def] is the default value, i.e. type T is not empty *)
Variables (T : Type) (def : T).
Local Notation nth := (nth def).

Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
rewrite size_ncons maxnE.
by case/orP: (leq_total n (size s)) => le; rewrite (eqP le) ?subnKC ?subnK.
Qed.

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof. by move=> i; rewrite nth_ncons => ->. Qed.

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
by move=> i _; rewrite nth_ncons addKn ifN // -ltnNge leq_addr.
Qed.

End LeftPad.